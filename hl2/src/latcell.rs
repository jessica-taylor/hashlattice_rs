use std::sync::{Arc, Mutex};
use std::ops::Deref;
use crate::lattice::Semilattice;


#[derive(Clone)]
pub struct LatCell<L> {
    value: Arc<Mutex<L>>,
    parent: Option<Box<LatCell<L>>>
}

impl<L : Semilattice> LatCell<L> {
    fn new(value: L) -> Self {
        Self {value: Arc::new(Mutex::new(value)), parent: None}
    }
    fn new_bottom() -> Self {
        Self::new(L::bottom())
    }
    fn get_value(&self) -> L {
        let value = self.value.lock().unwrap();
        return value.clone();
    }
    fn join_value(&self, other: &L) -> Result<(), String> {
        let mut value = self.value.lock().unwrap();
        value.join(other)
    }
    fn local_copy(&self) -> Self {
        let value = self.get_value();
        Self { value: Arc::new(Mutex::new(value)), parent: Some(Box::new(self.clone())) }
    }
    fn join_to_parent(&mut self) -> Result<(), String> {
        match &self.parent {
            None => Ok(()),
            Some(parent) => {
                let value = self.value.lock().unwrap();
                parent.join_value(value.deref())
            }
        }
    }
}


