pub type DigestOutput = u64;

pub trait Digestible {
    fn digest(&self) -> DigestOutput;
}
