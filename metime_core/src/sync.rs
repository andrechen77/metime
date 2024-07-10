use std::fmt::Debug;

use thiserror::Error;
use transaction::TransactionError;

pub mod client;
pub mod server;
pub mod transaction;

#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub struct ClientId(u64);

/// Error type for replaying transactions onto the tip of a timeline to extend
/// it.
#[derive(Error, Debug)]
pub enum FastForwardError {
    #[error("The client's basis version does not match the server's blessed version.")]
    OutdatedBasis,
    /// Indicates that the client's transaction sequence number does not match
    /// the number that the server has tracked for this client.
    #[error("The client's sequence number does not match the number that the server has tracked for the client.")]
    InvalidSequenceNumber,
    #[error("Client's transaction {index} could not be executed: {error}")]
    InvalidTransaction {
        #[source]
        error: TransactionError,
        index: usize,
    },
}

#[cfg(test)]
mod test {
    use super::{client::*, server::*, transaction::*, *};
    use crate::digest::{DigestOutput, Digestible};
    use std::{cell::RefCell, rc::Rc, vec};

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
                self.server.borrow().get_client_sequence_number(&self.client_id).unwrap(),
            )
        }

        async fn download_transactions_since(
            &self,
            version_digest: DigestOutput,
        ) -> Option<(Vec<VecOperation>, u64)> {
            let transactions =
                self.server.borrow_mut().get_transactions_since(version_digest)?.cloned().collect();
            let seq_num = self.server.borrow().get_client_sequence_number(&self.client_id).unwrap();
            Some((transactions, seq_num))
        }

        async fn push_transactions<'a, 'fut>(
            &self,
            transactions: impl Iterator<Item = &'a VecOperation>,
            basis_vesion_digest: DigestOutput,
            sequence_number: u64,
        ) -> Result<(), PushError> {
            Ok(self.server.borrow_mut().fast_forward_transactions(
                &self.client_id,
                transactions.cloned(),
                basis_vesion_digest,
                sequence_number,
            )?)
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
