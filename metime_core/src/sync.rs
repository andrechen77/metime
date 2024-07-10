use std::{
    collections::{HashMap, VecDeque},
    fmt::Debug,
};

use crate::digest::{DigestOutput, Digestible};

type Rollback<V> = Box<dyn Fn(&mut V)>;

/// A transaction that can be executed on some type `V`, modifying it.
pub trait Transaction<V> {
    /// Executes the transaction on the given `V`, modifying it. If the
    /// transaction is successful, returns a function that can be used to
    /// roll back the transaction; when given a `V` in the exact state after
    /// this transaction executed, the rollback is guaranteed to
    /// modify the `V` into the exact state before this transaction executed. If
    /// the execution is unsuccessful, the `V` must remain unchanged.
    fn execute(&self, value: &mut V) -> Result<Rollback<V>, TransactionError>;
}

/// Error type for executing transactions.
#[derive(Debug)]
pub enum TransactionError {
    Invalid,
}

/// Defines methods that a client can use to communicate with a server.
pub trait ServerApi<V: Digestible, T: Transaction<V>> {
    /// Downloads the most recent version of the value from the server, along
    /// with the next sequence number for this client.
    async fn download_whole(&self) -> (V, u64);

    /// Downloads the transactions that have been executed since the version
    /// with the given digest, along with the next sequence number for this
    /// client. Returns None if the given digest is not found on the server.
    async fn download_transactions_since(
        &self,
        version_digest: DigestOutput,
    ) -> Option<(Vec<T>, u64)>;

    /// Attempts to push the given transactions to the server. The
    /// interpretation is that the given transactions are executed on the
    /// version of the value with the given digest, and that the transactions
    /// start at the given sequence number for this client. Thus, the basis
    /// version digest must match the one on the server, and the given sequence
    /// number must match the next sequence number for this client.
    async fn push_transactions<'a, 'fut>(
        &self,
        transactions: impl Iterator<Item = &'a T>,
        basis_vesion_digest: DigestOutput,
        sequence_number: u64,
    ) -> Result<(), PushError>
    where
        T: 'a;
}

/// Error type for pushing transactions to the server.
pub enum PushError {
    /// Indicates that the client's basis version does not match the blessed
    /// version on the server.
    OutdatedBasis,
    /// Indicates that the client's transaction sequence number does not match
    /// the number that the server has tracked for this client.
    InvalidSequenceNumber,
    /// Indicates that one of the client's transactions could not be executed.
    InvalidTransaction { error: TransactionError, index: usize },
}

/// Stores a value of type `V` that is synced with a server.
pub struct ClientSync<V: Digestible, T: Transaction<V>, S: ServerApi<V, T>> {
    /// A hash of the most recent version of the value obtained from the server,
    /// called the "basis version". This is used to quickly check if this
    /// client's basis version matches the server's blessed version upon
    /// syncing.
    basis_version_digest: u64,
    /// A working copy of the value, known only to this client. This value was
    /// obtained by executing all `self.unsynced_transactions` onto the basis
    /// version.
    working_copy: V,
    /// The transactions that were executed onto the basis version to obtain
    /// `self.working_copy`, along with their corresponding rollback functions.
    unsynced_transactions: Vec<(T, Rollback<V>)>,
    /// The sequence number for this client of the first transaction in
    /// `self.unsynced_transactions`.
    sequence_number: u64,
    /// The server API that this client uses to communicate with the server.
    server_api: S,
}

impl<V, T, S> ClientSync<V, T, S>
where
    V: Digestible + Debug,
    T: Transaction<V> + Debug,
    S: ServerApi<V, T>,
{
    /// Creates a new `ClientSync` with the given `basis_version`.
    pub fn with_basis_version(server_api: S, basis_version: V, sequence_number: u64) -> Self {
        let basis_version_digest = basis_version.digest();
        Self {
            basis_version_digest,
            working_copy: basis_version,
            unsynced_transactions: Vec::new(),
            sequence_number,
            server_api,
        }
    }

    /// Creates a new `ClientSync` with the server's most recent version.
    pub async fn with_server_sync(server_api: S) -> Self {
        let (basis_version, sequence_number) = server_api.download_whole().await;
        Self::with_basis_version(server_api, basis_version, sequence_number)
    }

    /// Syncs the client with the server, pushing all unsynced transactions. If
    /// the client's basis version or sequence number is different from the
    /// server's blessed version, the client will request the server to send the
    /// latest blessed version, apply all unsynced transactions to that version,
    /// and attempt to push again.
    pub async fn synchronize_value(&mut self) {
        loop {
            match self
                .server_api
                .push_transactions(
                    self.unsynced_transactions.iter().map(|(forward, _rollback)| forward),
                    self.basis_version_digest,
                    self.sequence_number,
                )
                .await
            {
                Ok(()) => {
                    self.basis_version_digest = self.working_copy.digest();
                    self.sequence_number +=
                        u64::try_from(self.unsynced_transactions.len()).unwrap();
                    self.unsynced_transactions.clear();
                    break;
                }
                Err(PushError::OutdatedBasis) => {
                    // get our working copy to match the blessed version of the
                    // value from the server. download the transactions that were
                    // missed
                    if let Some((missed_transactions, sequence_number)) =
                        self.server_api.download_transactions_since(self.basis_version_digest).await
                    {
                        // forget transactions that are already synced
                        let num_pre_synced =
                            usize::try_from(sequence_number.wrapping_sub(self.sequence_number))
                                .unwrap();
                        self.unsynced_transactions.drain(..num_pre_synced);
                        self.sequence_number = sequence_number;

                        // roll back the transactions that we made, resulting in the
                        // working copy being at the basis version
                        for (_forward, rollback) in self.unsynced_transactions.iter().rev() {
                            rollback(&mut self.working_copy);
                        }

                        // apply the missed transactions from the server, resulting
                        // in the working copy being at the blessed version
                        execute_all_or_roll_back(
                            &mut self.working_copy,
                            missed_transactions.into_iter(),
                        )
                        .expect("transactions from the server should be valid");
                        self.basis_version_digest = self.working_copy.digest();
                    } else {
                        // the server does not have the basis version that we have, so download anew.
                        let (blessed_version, sequence_number) =
                            self.server_api.download_whole().await;
                        self.sequence_number = sequence_number;
                        self.working_copy = blessed_version;
                        self.basis_version_digest = self.working_copy.digest();
                    }

                    // attempt to replay our unsynced transactions onto the
                    // blessed version
                    for (transaction, _rollback) in &self.unsynced_transactions {
                        if let Err(_err) = transaction.execute(&mut self.working_copy) {
                            // the client should decide somehow how to proceed
                            todo!();
                        }
                    }

                    // enter another iteration of the loop to try pushing again
                }
                Err(PushError::InvalidSequenceNumber) => todo!(),
                Err(PushError::InvalidTransaction { .. }) => todo!(),
            }
        }
    }

    pub fn apply_transaction(&mut self, transaction: T) {
        let rollback =
            transaction.execute(&mut self.working_copy).expect("transactions should be valid");
        self.unsynced_transactions.push((transaction, rollback));
    }

    pub fn get_working_copy(&self) -> &V {
        &self.working_copy
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub struct ClientId(u64);

#[derive(Default)]
pub struct ClientInfo {
    /// The next sequence number that this client should use when pushing
    /// transactions.
    sequence_number: u64,
    /// The digest of the version that this client has last seen. It is assumed
    /// that if a client requests transactions since this digest, then it will
    /// never request a digest of an earlier version. None means that the client
    /// has not confirmed that they have any version of the value.
    last_digest_confirmed: Option<DigestOutput>, // TODO keep this updated as the client makes requests
}

pub struct ServerSync<V: Digestible, T: Transaction<V>> {
    /// The most up-to-date version of the value that the server has. This
    /// version is the result of all the transactions that have been
    /// successfully pushed to the server up to this point.
    blessed_version: V,
    /// The most recent transactions known to the server, stored along with the
    /// digest of the value that each transaction was applied to.
    transactions: VecDeque<(DigestOutput, T)>,
    client_info: HashMap<ClientId, ClientInfo>,
}

impl<V, T> ServerSync<V, T>
where
    V: Digestible + Debug,
    T: Transaction<V> + Debug,
{
    pub fn new(blessed_version: V) -> Self {
        Self { blessed_version, transactions: VecDeque::new(), client_info: HashMap::new() }
    }

    /// Gets the most recent version of the value.
    pub fn get_blessed(&self) -> &V {
        &self.blessed_version
    }

    pub fn register_client(&mut self, client_id: ClientId) {
        self.client_info.insert(client_id, ClientInfo::default());
    }

    pub fn get_client_info(&self, client: &ClientId) -> Option<&ClientInfo> {
        self.client_info.get(client)
    }

    pub fn get_transactions_since(
        &mut self,
        digest: DigestOutput,
    ) -> Option<impl Iterator<Item = &T>> {
        // find the index of the transaction with the given digest
        let index = self
            .transactions
            .iter()
            .rposition(|(transaction_digest, _)| *transaction_digest == digest)?;

        Some(self.transactions.iter().skip(index).map(|(_, transaction)| transaction))
    }

    pub fn push_transactions(
        &mut self,
        client: &ClientId,
        transactions: impl Iterator<Item = T>,
        basis_version_digest: DigestOutput,
        sequence_number: u64,
    ) -> Result<(), PushError> {
        let client_info = self.client_info.get_mut(client).unwrap();

        // check if the client's basis version matches the server's blessed version
        if self.blessed_version.digest() != basis_version_digest {
            return Err(PushError::OutdatedBasis);
        }

        // check if the client's sequence number matches sequence number for that client on the server
        if client_info.sequence_number != sequence_number {
            return Err(PushError::InvalidSequenceNumber);
        }

        // apply the transactions to the blessed version
        let history =
            match execute_all_or_roll_back(&mut self.blessed_version, transactions.into_iter()) {
                Ok(history) => history,
                Err((error, index)) => {
                    return Err(PushError::InvalidTransaction { error, index });
                }
            };
        let num_transactions = history.len();
        self.transactions.extend(history);

        // update the client's sequence number
        client_info.sequence_number += u64::try_from(num_transactions).unwrap();

        Ok(())
    }
}

/// Executes all the given transactions on the given value and returns a vector
/// containing the digests of each intermediate value and the corresponding
/// transaction that acted on that value. If one of the transactions fails, then
/// the entire process is rolled back as if nothing happened at all. The error
/// and index of the transaction that failed is returned.
fn execute_all_or_roll_back<V, I, T>(
    value: &mut V,
    transactions: I,
) -> Result<Vec<(DigestOutput, T)>, (TransactionError, usize)>
where
    V: Digestible,
    I: Iterator<Item = T>,
    T: Transaction<V>,
{
    let mut rollback_stack = Vec::new();
    let mut history = Vec::new();
    for (i, transaction) in transactions.into_iter().enumerate() {
        let digest = value.digest();
        match transaction.execute(value) {
            Ok(rollback) => {
                rollback_stack.push(rollback);
                history.push((digest, transaction));
            }
            Err(err) => {
                for rollback in rollback_stack.into_iter().rev() {
                    rollback(value);
                }
                return Err((err, i));
            }
        };
    }
    Ok(history)
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc, vec};

    use super::*;

    #[derive(Debug, Clone)]
    enum VecOperation {
        Push(u32),
        Pop(u32), // expects the given value to be popped
    }

    impl Transaction<Vec<u32>> for VecOperation {
        fn execute(
            &self,
            vec: &mut Vec<u32>,
        ) -> Result<Box<dyn Fn(&mut Vec<u32>)>, TransactionError> {
            match self {
                &VecOperation::Push(value) => {
                    vec.push(value);
                    Ok(Box::new(move |vec| {
                        let result = vec.pop().unwrap();
                        assert!(result == value, "rollback from different state than expected")
                    }))
                }
                &VecOperation::Pop(expected) => {
                    let Some(popped) = vec.pop() else {
                        return Err(TransactionError::Invalid);
                    };
                    if popped == expected {
                        Ok(Box::new(move |value| {
                            value.push(popped);
                        }))
                    } else {
                        Err(TransactionError::Invalid)
                    }
                }
            }
        }
    }

    impl Digestible for Vec<u32> {
        fn digest(&self) -> DigestOutput {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::hash::DefaultHasher::new();
            self.hash(&mut hasher);
            hasher.finish()
        }
    }

    struct ServerWrapper {
        client_id: ClientId,
        server: Rc<RefCell<ServerSync<Vec<u32>, VecOperation>>>,
    }

    impl ServerWrapper {
        fn new(server: Rc<RefCell<ServerSync<Vec<u32>, VecOperation>>>) -> Self {
            let client_id = ClientId(rand::random());
            server.borrow_mut().register_client(client_id.clone());
            Self { client_id, server }
        }
    }

    impl ServerApi<Vec<u32>, VecOperation> for ServerWrapper {
        async fn download_whole(&self) -> (Vec<u32>, u64) {
            (
                self.server.borrow().get_blessed().clone(),
                self.server.borrow().get_client_info(&self.client_id).unwrap().sequence_number,
            )
        }

        async fn download_transactions_since(
            &self,
            version_digest: DigestOutput,
        ) -> Option<(Vec<VecOperation>, u64)> {
            let transactions =
                self.server.borrow_mut().get_transactions_since(version_digest)?.cloned().collect();
            let seq_num =
                self.server.borrow().get_client_info(&self.client_id).unwrap().sequence_number;
            Some((transactions, seq_num))
        }

        async fn push_transactions<'a, 'fut>(
            &self,
            transactions: impl Iterator<Item = &'a VecOperation>,
            basis_vesion_digest: DigestOutput,
            sequence_number: u64,
        ) -> Result<(), PushError> {
            self.server.borrow_mut().push_transactions(
                &self.client_id,
                transactions.cloned(),
                basis_vesion_digest,
                sequence_number,
            )
        }
    }

    #[test]
    fn transactions_work() {
        let initial_version = vec![1, 2, 3];
        let server = Rc::new(RefCell::new(ServerSync::new(initial_version.clone())));
        let mut synced =
            ClientSync::with_basis_version(ServerWrapper::new(server), initial_version, 0);
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
    }

    #[tokio::test]
    async fn initial_sync_works() {
        let initial_version = vec![1, 2, 3];
        let server = Rc::new(RefCell::new(ServerSync::new(initial_version)));
        let mut synced = ClientSync::with_server_sync(ServerWrapper::new(server)).await;
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        ()
    }

    #[tokio::test]
    async fn invalid_initial_value_is_corrected() {
        let server = Rc::new(RefCell::new(ServerSync::new(vec![1, 2, 3])));
        let mut synced =
            ClientSync::with_basis_version(ServerWrapper::new(server), vec![11, 22, 33], 0);
        assert_eq!(synced.get_working_copy(), &vec![11, 22, 33]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![11, 22, 33, 4, 5, 6]);
        synced.synchronize_value().await;
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        ()
    }

    #[tokio::test]
    async fn multiple_clients_clean_sync() {
        let server = Rc::new(RefCell::new(ServerSync::new(vec![1, 2, 3])));
        let mut alice = ClientSync::with_server_sync(ServerWrapper::new(server.clone())).await;
        let mut bob = ClientSync::with_server_sync(ServerWrapper::new(server.clone())).await;

        bob.apply_transaction(VecOperation::Push(7));
        bob.apply_transaction(VecOperation::Push(8));
        bob.apply_transaction(VecOperation::Push(9));

        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 7, 8, 9]);

        alice.apply_transaction(VecOperation::Push(4));
        alice.apply_transaction(VecOperation::Push(5));
        alice.apply_transaction(VecOperation::Push(6));

        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(server.borrow().get_blessed(), &vec![1, 2, 3]);

        alice.synchronize_value().await;

        assert_eq!(server.borrow().get_blessed(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 7, 8, 9]);

        bob.synchronize_value().await;

        assert_eq!(server.borrow().get_blessed(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        alice.synchronize_value().await;

        assert_eq!(server.borrow().get_blessed(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        ()
    }
}
