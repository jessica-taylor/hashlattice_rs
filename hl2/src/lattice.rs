
pub trait Semilattice : Clone + Send + Sync {
    fn bottom() -> Self;
    fn is_elem(&self) -> Result<(), String>;
    fn join(&mut self, other: &Self) -> Result<(), String>;
}
