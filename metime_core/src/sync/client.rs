use thiserror::Error;

use crate::digest::{DigestOutput, Digestible};
use std::fmt::Debug;

use super::{
    transaction::{self, Rollback, Transaction},
    FastForwardError, Steal,
};

/// Stores a value of type `V` that is synced with a server.
pub struct ClientSync<V, S>
where
    V: Digestible + Steal<S::DownloadWhole>,
    S: ServerApi<V>,
{
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
    /// `self.working_copy`
    unsynced_transactions: Vec<S::Tx>,
    /// The corresponding rollback functions for each of the unsynced
    /// transactions. This must always have the same length as
    /// `self.unsynced_transactions`.
    rollbacks: Vec<Rollback<V>>,
    /// The sequence number for this client of the first transaction in
    /// `self.unsynced_transactions`.
    sequence_number: u64,
    /// The server API that this client uses to communicate with the server.
    server_api: S,
}

impl<V, S> ClientSync<V, S>
where
    V: Digestible + Debug + Steal<S::DownloadWhole>,
    S: ServerApi<V>,
    S::DownloadWhole: Into<V>,
{
    /// Creates a new `ClientSync` with the server's most recent version.
    pub async fn with_server_sync(server_api: S) -> Self {
        let (download, sequence_number) = server_api.download_whole().await;
        Self::with_basis_version(server_api, download.into(), sequence_number)
    }
}

impl<V, S> ClientSync<V, S>
where
    V: Digestible + Debug + Steal<S::DownloadWhole>,
    S: ServerApi<V>,
{
    /// Creates a new `ClientSync` with the given `basis_version`.
    pub fn with_basis_version(server_api: S, basis_version: V, sequence_number: u64) -> Self {
        let basis_version_digest = basis_version.digest();
        Self {
            basis_version_digest,
            working_copy: basis_version,
            unsynced_transactions: Vec::new(),
            rollbacks: Vec::new(),
            sequence_number,
            server_api,
        }
    }

    /// Syncs the client with the server, pushing all unsynced transactions. If
    /// the client's basis version or sequence number is different from the
    /// server's blessed version, the client will request the latest blessed
    /// version from the server, rebase all of our own unsynced transactions to
    /// that version, and attempt to push again.
    pub async fn synchronize_value(&mut self) -> Result<(), CommunicationError> {
        loop {
            match self
                .server_api
                .push_transactions(
                    self.unsynced_transactions.iter(),
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
                    self.rollbacks.clear();
                    return Ok(());
                }
                Err(PushError::FastForwardError(FastForwardError::OutdatedBasis)) => {
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
                        self.rollbacks.drain(..num_pre_synced);
                        self.sequence_number = sequence_number;

                        // roll back the transactions that we made, resulting in the
                        // working copy being at the basis version
                        for rollback in self.rollbacks.iter().rev() {
                            rollback(&mut self.working_copy);
                        }

                        // apply the missed transactions from the server, resulting
                        // in the working copy being at the blessed version
                        transaction::execute_all_or_roll_back(
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
                        self.working_copy.steal(blessed_version);
                        self.basis_version_digest = self.working_copy.digest();
                    }

                    // attempt to replay our unsynced transactions onto the
                    // blessed version
                    for transaction in &self.unsynced_transactions {
                        if let Err(_err) = transaction.execute(&mut self.working_copy) {
                            // the client should decide somehow how to proceed
                            todo!();
                        }
                    }

                    // enter another iteration of the loop to try pushing again
                }
                Err(PushError::FastForwardError(FastForwardError::InvalidSequenceNumber)) => {
                    todo!()
                }
                Err(PushError::FastForwardError(FastForwardError::InvalidTransaction {
                    ..
                })) => todo!(),
                Err(PushError::CommunicationError(err)) => {
                    // assume that our communication did not go through
                    return Err(err);
                }
            }
        }
    }

    pub fn apply_transaction(&mut self, transaction: S::Tx) {
        let rollback =
            transaction.execute(&mut self.working_copy).expect("transactions should be valid");
        self.unsynced_transactions.push(transaction);
        self.rollbacks.push(rollback);
    }

    pub fn get_working_copy(&self) -> &V {
        &self.working_copy
    }

    pub fn get_unsynced_transactions(&self) -> &[S::Tx] {
        &self.unsynced_transactions
    }
}

/// Defines methods that a client can use to communicate with a server.
pub trait ServerApi<V: Digestible + Steal<Self::DownloadWhole>> {
    /// The type that is returned when the entire value is downloaded from the
    /// server.
    type DownloadWhole;
    type Tx: Transaction<V>;

    /// Downloads the most recent version of the value from the server, along
    /// with the next sequence number for this client.
    async fn download_whole(&self) -> (Self::DownloadWhole, u64);

    /// Downloads the transactions that have been executed since the version
    /// with the given digest, along with the next sequence number for this
    /// client. Returns None if the given digest is not found on the server.
    async fn download_transactions_since(
        &self,
        version_digest: DigestOutput,
    ) -> Option<(Vec<Self::Tx>, u64)>;

    /// Attempts to push the given transactions to the server. The
    /// interpretation is that the given transactions are executed on the
    /// version of the value with the given digest, and that the transactions
    /// start at the given sequence number for this client. Thus, the basis
    /// version digest must match the one on the server, and the given sequence
    /// number must match the next sequence number for this client.
    async fn push_transactions<'a, 'fut>(
        &self,
        transactions: impl Iterator<Item = &'a Self::Tx>,
        basis_vesion_digest: DigestOutput,
        sequence_number: u64,
    ) -> Result<(), PushError>
    where
        Self::Tx: 'a;
}

#[derive(Error, Debug)]
pub enum PushError {
    #[error(transparent)]
    FastForwardError(#[from] FastForwardError),
    #[error(transparent)]
    CommunicationError(#[from] CommunicationError),
}

#[derive(Error, Debug)]
pub enum CommunicationError {
    // TODO flesh this out
    #[error("Unable to communicate with the server.")]
    NetworkError,
}
