use thiserror::Error;

use crate::digest::{DigestOutput, Digestible};

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

pub type Rollback<V> = Box<dyn Fn(&mut V)>;

/// Error type for executing transactions.
#[derive(Debug, Error)]
pub enum TransactionError {
    // TODO make this more specific
    #[error("The transaction is invalid somehow.")]
    Invalid,
}

/// Executes all the given transactions on the given value and returns a vector
/// containing the digests of each intermediate value and the corresponding
/// transaction that acted on that value. If one of the transactions fails, then
/// the entire process is rolled back as if nothing happened at all. The error
/// and index of the transaction that failed is returned.
pub fn execute_all_or_roll_back<V, I, T>(
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
