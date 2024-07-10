use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;

use crate::digest::{DigestOutput, Digestible};

use super::transaction::{self, Transaction};
use super::{ClientId, FastForwardError};

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

    pub fn get_client_sequence_number(&self, client: &ClientId) -> Option<u64> {
        self.client_info.get(client).map(|info| info.sequence_number)
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

    pub fn fast_forward_transactions(
        &mut self,
        client: &ClientId,
        transactions: impl Iterator<Item = T>,
        basis_version_digest: DigestOutput,
        sequence_number: u64,
    ) -> Result<(), FastForwardError> {
        let client_info = self.client_info.get_mut(client).unwrap();

        // check if the client's basis version matches the server's blessed version
        if self.blessed_version.digest() != basis_version_digest {
            return Err(FastForwardError::OutdatedBasis);
        }

        // check if the client's sequence number matches sequence number for that client on the server
        if client_info.sequence_number != sequence_number {
            return Err(FastForwardError::InvalidSequenceNumber);
        }

        // apply the transactions to the blessed version
        let history = match transaction::execute_all_or_roll_back(
            &mut self.blessed_version,
            transactions.into_iter(),
        ) {
            Ok(history) => history,
            Err((error, index)) => {
                return Err(FastForwardError::InvalidTransaction { error, index });
            }
        };
        let num_transactions = history.len();
        self.transactions.extend(history);

        // update the client's sequence number
        client_info.sequence_number += u64::try_from(num_transactions).unwrap();

        Ok(())
    }
}
