use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;

use super::lattice::{Semilattice, LatticeReadDB, LatticeWriteDB};

pub struct MemoryLatticeDB<L: Semilattice> {
    maxes: Mutex<BTreeMap<L::LID, L::Value>>,
}

impl<L: Semilattice> MemoryLatticeDB<L> {
    pub fn new() -> Self {
        MemoryLatticeDB {
            maxes: Mutex::new(BTreeMap::new()),
        }
    }
}

#[async_trait]
impl<L: Semilattice> LatticeReadDB<L> for MemoryLatticeDB<L> {
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        self.maxes.lock().unwrap().get(&lid).cloned()
    }
}

#[async_trait]
impl<L: Semilattice> LatticeWriteDB<L> for MemoryLatticeDB<L> {
    async fn pin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }

    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String> {
        self.maxes.lock().unwrap().insert(lid, value);
        Ok(())
    }

    async fn unpin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }
}
