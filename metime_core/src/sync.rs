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
    use std::{cell::{Ref, RefCell}, vec};

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        next_client_id: RefCell<u64>,
        num_successes_to_ignore: RefCell<usize>,
        server: RefCell<ServerSync<Vec<u32>, VecOperation>>,
    }

    impl ServerWrapper {
        fn new(server: ServerSync<Vec<u32>, VecOperation>) -> Self {
            Self { next_client_id: RefCell::new(0), num_successes_to_ignore: RefCell::new(0), server: RefCell::new(server) }
        }

        fn get_handle(&self) -> ServerHandle<'_> {
            let client_id = ClientId(*self.next_client_id.borrow());
            *self.next_client_id.borrow_mut() += 1;
            self.server.borrow_mut().register_client(client_id.clone());
            ServerHandle { client_id, server: &*self }
        }

        fn get_blessed(&self) -> Ref<Vec<u32>> {
            Ref::map(self.server.borrow(), |server| server.get_blessed())
        }

        fn download_whole(&self, client_id: &ClientId) -> (Vec<u32>, u64) {
            (
                self.server.borrow().get_blessed().clone(),
                self.server.borrow().get_client_sequence_number(client_id).unwrap(),
            )
        }

        fn download_transactions_since(
            &self,
            version_digest: DigestOutput,
            client_id: &ClientId,
        ) -> Option<(Vec<VecOperation>, u64)> {
            let transactions =
                self.server.borrow_mut().get_transactions_since(version_digest)?.cloned().collect();
            let seq_num = self.server.borrow().get_client_sequence_number(client_id).unwrap();
            Some((transactions, seq_num))
        }

        fn push_transactions<'a, 'fut>(
            &self,
            transactions: impl Iterator<Item = &'a VecOperation>,
            basis_vesion_digest: DigestOutput,
            sequence_number: u64,
            client_id: &ClientId,
        ) -> Result<(), PushError> {
            let result = self.server.borrow_mut().fast_forward_transactions(
                client_id,
                transactions.cloned(),
                basis_vesion_digest,
                sequence_number,
            );
            match result {
                Ok(ok) => {
                    let mut num_successes_to_ignore = self.num_successes_to_ignore.borrow_mut();
                    if *num_successes_to_ignore == 0 {
                        Ok(ok)
                    } else {
                        *num_successes_to_ignore -= 1;
                        Err(PushError::CommunicationError(CommunicationError::NetworkError))
                    }

                }
                Err(err) => Err(PushError::FastForwardError(err)),
            }
        }

        fn set_num_successes_to_ignore(&self, num_successes_to_ignore: usize) {
            *self.num_successes_to_ignore.borrow_mut() = num_successes_to_ignore;
        }
    }

    /// Implements `ServerApi`,  allowing clients to communicate with the
    /// server.
    struct ServerHandle<'handle> {
        client_id: ClientId,
        server: &'handle ServerWrapper,
    }

    impl<'handle> ServerApi<Vec<u32>, VecOperation> for ServerHandle<'handle> {
        async fn download_whole(&self) -> (Vec<u32>, u64) {
            self.server.download_whole(&self.client_id)
        }

        async fn download_transactions_since(
            &self,
            version_digest: DigestOutput,
        ) -> Option<(Vec<VecOperation>, u64)> {
            self.server.download_transactions_since(version_digest, &self.client_id)
        }

        async fn push_transactions<'a, 'fut>(
            &self,
            transactions: impl Iterator<Item = &'a VecOperation>,
            basis_vesion_digest: DigestOutput,
            sequence_number: u64,
        ) -> Result<(), PushError> {
            self.server.push_transactions(transactions, basis_vesion_digest, sequence_number, &self.client_id)
        }
    }

    #[test]
    fn transactions_work() {
        let initial_version = vec![1, 2, 3];
        let server = ServerWrapper::new(ServerSync::new(initial_version.clone()));
        let mut synced =
            ClientSync::with_basis_version(server.get_handle(), initial_version, 0);
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
    }

    #[tokio::test]
    async fn initial_sync_works() {
        let initial_version = vec![1, 2, 3];
        let server = ServerWrapper::new(ServerSync::new(initial_version));
        let mut synced = ClientSync::with_server_sync(server.get_handle()).await;
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        ()
    }

    #[tokio::test]
    async fn invalid_initial_value_is_corrected() {
        let server = ServerWrapper::new(ServerSync::new(vec![1, 2, 3]));
        let mut synced =
            ClientSync::with_basis_version(server.get_handle(), vec![11, 22, 33], 0);
        assert_eq!(synced.get_working_copy(), &vec![11, 22, 33]);
        synced.apply_transaction(VecOperation::Push(4));
        synced.apply_transaction(VecOperation::Push(5));
        synced.apply_transaction(VecOperation::Push(6));
        assert_eq!(synced.get_working_copy(), &vec![11, 22, 33, 4, 5, 6]);
        synced.synchronize_value().await.unwrap();
        assert_eq!(synced.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        ()
    }

    #[tokio::test]
    async fn multiple_clients_clean_sync() {
        let server = ServerWrapper::new(ServerSync::new(vec![1, 2, 3]));
        let mut alice = ClientSync::with_server_sync(server.get_handle()).await;
        let mut bob = ClientSync::with_server_sync(server.get_handle()).await;

        bob.apply_transaction(VecOperation::Push(7));
        bob.apply_transaction(VecOperation::Push(8));
        bob.apply_transaction(VecOperation::Push(9));

        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 7, 8, 9]);

        alice.apply_transaction(VecOperation::Push(4));
        alice.apply_transaction(VecOperation::Push(5));
        alice.apply_transaction(VecOperation::Push(6));

        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(*server.get_blessed(), vec![1, 2, 3]);

        alice.synchronize_value().await.unwrap();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 7, 8, 9]);

        bob.synchronize_value().await.unwrap();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        alice.synchronize_value().await.unwrap();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(alice.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(bob.get_working_copy(), &vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        ()
    }

    #[tokio::test]
    async fn handles_synced_but_no_reply() {
        let server = ServerWrapper::new(ServerSync::new(vec![1, 2, 3]));
        let mut client = ClientSync::with_server_sync(server.get_handle()).await;

        client.apply_transaction(VecOperation::Push(4));
        client.apply_transaction(VecOperation::Push(5));
        server.set_num_successes_to_ignore(1);
        client.synchronize_value().await.unwrap_err();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5]);
        assert_eq!(*client.get_working_copy(), vec![1, 2, 3, 4, 5]);
        assert_eq!(client.get_unsynced_transactions(), &[VecOperation::Push(4), VecOperation::Push(5)]);

        client.apply_transaction(VecOperation::Push(6));
        client.synchronize_value().await.unwrap();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(*client.get_working_copy(), vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(client.get_unsynced_transactions(), &[]);

        ()
    }

    #[tokio::test]
    async fn multiple_clients_handle_synced_but_no_reply() {
        let server = ServerWrapper::new(ServerSync::new(vec![1, 2, 3]));
        let mut alice = ClientSync::with_server_sync(server.get_handle()).await;
        let mut bob = ClientSync::with_server_sync(server.get_handle()).await;

        alice.apply_transaction(VecOperation::Push(4));
        bob.apply_transaction(VecOperation::Push(5));
        server.set_num_successes_to_ignore(2);
        // alice successfully pushes but doesn't get the confirmation
        alice.synchronize_value().await.unwrap_err();
        // bob gets alice's changes, rebases, and pushes again, but doesn't get the confirmation
        bob.synchronize_value().await.unwrap_err();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5]);
        assert_eq!(*alice.get_working_copy(), vec![1, 2, 3, 4]);
        assert_eq!(*bob.get_working_copy(), vec![1, 2, 3, 4, 5]);
        assert_eq!(alice.get_unsynced_transactions(), &[VecOperation::Push(4)]);
        assert_eq!(bob.get_unsynced_transactions(), &[VecOperation::Push(5)]);

        alice.apply_transaction(VecOperation::Push(6));
        bob.apply_transaction(VecOperation::Push(7));
        alice.synchronize_value().await.unwrap();
        bob.synchronize_value().await.unwrap();

        assert_eq!(*server.get_blessed(), vec![1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(*alice.get_working_copy(), vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(*bob.get_working_copy(), vec![1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(alice.get_unsynced_transactions(), &[]);
        assert_eq!(bob.get_unsynced_transactions(), &[]);

        alice.synchronize_value().await.unwrap();
        assert_eq!(*alice.get_working_copy(), vec![1, 2, 3, 4, 5, 6, 7]);

        ()
    }
}
