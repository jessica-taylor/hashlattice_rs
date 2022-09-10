use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use futures::{join, future::join_all};

use super::lattice::{LatGraph, LatticeReadDB, LatticeWriteDB};

pub struct MemoryLatticeDB<L: LatGraph> {
    lattice: Arc<L>,
    maxes: Mutex<BTreeMap<L::LID, L::Value>>,
}

impl<L: LatGraph> MemoryLatticeDB<L> {
    pub fn new(lattice: Arc<L>) -> Self {
        MemoryLatticeDB {
            lattice,
            maxes: Mutex::new(BTreeMap::new()),
        }
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeReadDB<L> for MemoryLatticeDB<L> {
    fn get_lattice(&self) -> Arc<L> {
        self.lattice.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        self.maxes.lock().unwrap().get(&lid).cloned()
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeWriteDB<L> for MemoryLatticeDB<L> {
    async fn pin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }

    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String> {
        let default = self.lattice.default(lid.clone())?;
        let current = self.clone().get_lattice_max(lid.clone()).await.unwrap_or(default.clone());
        let (current_deps, value_deps) = join!(
            self.lattice.clone().dependencies(self.clone(), lid.clone(), current.clone()),
            self.lattice.clone().dependencies(self.clone(), lid.clone(), value.clone()));
        let self2 = self.clone();
        let kvs = join_all(current_deps?.union(&value_deps?).into_iter().map(move |lid| {
            let self3 = self2.clone();
            let default = default.clone();
            async move {
                (lid.clone(), self3.clone().get_lattice_max(lid.clone()).await.unwrap_or(default.clone()))
            }
        })).await;
        let joined = self.lattice.clone().join(lid.clone(), BTreeMap::from_iter(kvs), current.clone(), value).await?;
        if joined != current {
            self.maxes.lock().unwrap().insert(lid, joined);
        }
        Ok(())
    }

    async fn unpin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        Ok(())
    }
}
