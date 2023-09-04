use std::sync::Arc;
use std::ops::Deref;

pub trait Semilattice : Clone + Send + Sync {
    fn bottom() -> Self;
    fn is_elem(&self) -> Result<(), String>;
    fn join(&mut self, other: &Self) -> Result<(), String>;
}

impl<L : Semilattice> Semilattice for Arc<L> {
    fn bottom() -> Self {
        Arc::new(L::bottom())
    }
    fn is_elem(&self) -> Result<(), String> {
        self.is_elem()
    }
    fn join(&mut self, other: &Self) -> Result<(), String> {
        let mut val: L = self.as_ref().clone();
        val.join(other.as_ref())?;
        *self = Arc::new(val);
        Ok(())
    }
}
