use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;

use super::lattice::{Semilattice, LatticeReadDB, LatticeWriteDB};

pub struct MemoryLatticeDB<L: Semilattice> {
    lattice: Arc<L>,
    maxes: Mutex<BTreeMap<L::LID, L::Value>>,
}

impl<L: Semilattice> MemoryLatticeDB<L> {
    pub fn new(lattice: Arc<L>) -> Self {
        MemoryLatticeDB {
            lattice,
            maxes: Mutex::new(BTreeMap::new()),
        }
    }
}

#[async_trait]
impl<L: Semilattice + 'static> LatticeReadDB<L> for MemoryLatticeDB<L> {
    fn get_lattice(&self) -> Arc<L> {
        self.lattice.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        self.maxes.lock().unwrap().get(&lid).cloned()
    }
}

#[async_trait]
impl<L: Semilattice + 'static> LatticeWriteDB<L> for MemoryLatticeDB<L> {
    async fn pin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }

    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String> {
        let default = self.lattice.default(lid.clone())?;
        let current = self.clone().get_lattice_max(lid.clone()).await.unwrap_or(default);
        let joined = self.lattice.clone().join(lid.clone(), self.clone(), current.clone(), value).await?;
        if joined != current {
            self.maxes.lock().unwrap().insert(lid, joined);
        }
        Ok(())
    }

    async fn unpin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }
}
