use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use async_recursion::async_recursion;
use futures::{join, future::join_all};

use super::lattice::{LatGraph, LatticeReadDB, LatticeWriteDB, DependencyLatticeDB, MapLatticeReadDB};


// how to merge values from two different dbs???
// first: get comparators for both values in their respective dbs, and associated dependency sets
// second: recurse into unequal dependencies, and merge the values
// third: create a small db with just the dependencies
// fourth: get comparators for the original values in the small db
// fifth: join the comparators, and get the final value
// sixth: put the final value in the original dbs
//
// recursion caches results to avoid re-doing work
//
// after all recursion is done, update all dependents of updated values in both dbs, by joining
// with default
//
// oh wait, another problem... when dep vals change, dep keys also change!

#[async_recursion]
async fn merge_dbs<
    L: LatGraph + 'static,
    D1: LatticeWriteDB<L::LID, L::Value, L::Cmp> + 'static,
    D2: LatticeWriteDB<L::LID, L::Value, L::Cmp> + 'static
>(latgraph: Arc<L>, db1: Arc<D1>, db2: Arc<D2>, lid: L::LID) -> Result<L::Value, String> {
    let default = latgraph.default(lid.clone())?;
    let (v1, v2) = join!(db1.clone().get_lattice_max(lid.clone()), db2.clone().get_lattice_max(lid.clone()));
    let v1 = v1.unwrap_or_else(|| default.clone());
    let v2 = v2.unwrap_or_else(|| default.clone());
    let dep_db1 = Arc::new(DependencyLatticeDB::new(db1.clone()));
    let dep_db2 = Arc::new(DependencyLatticeDB::new(db2.clone()));
    let (c1, c2) = join!(latgraph.clone().get_comparable(dep_db1.clone(), lid.clone(), v1.clone()),
                         latgraph.clone().get_comparable(dep_db2.clone(), lid.clone(), v2.clone()));
    let c1 = c1?;
    let c2 = c2?;
    let deps1 = dep_db1.deps();
    let deps2 = dep_db2.deps();
    let mut dep_vals = BTreeMap::new();
    for (k1, v1) in deps1.iter() {
        if deps2.get(k1) != Some(v1) {
            dep_vals.insert(k1.clone(), merge_dbs(latgraph.clone(), db1.clone(), db2.clone(), k1.clone()).await?);
        }
    }
    // TODO: re-does work
    for (k2, v2) in deps2.iter() {
        if deps1.get(k2) != Some(v2) {
            dep_vals.insert(k2.clone(), merge_dbs(latgraph.clone(), db1.clone(), db2.clone(), k2.clone()).await?);
        }
    }
    let dep_db = Arc::new(MapLatticeReadDB::new(latgraph.clone(), dep_vals));
    let (c1, c2) = join!(latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), v1.clone()),
                         latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), v2.clone()));
    let c1 = c1?;
    let c2 = c2?;

    let joined = latgraph.join(lid.clone(), c1, c2)?;
    let (res1, res2) = join!(db1.put_lattice_value(lid.clone(), joined.clone()),
                             db2.put_lattice_value(lid.clone(), joined.clone()));
    res1?;
    res2?;
    Ok(joined)
}

pub struct MemoryLatticeDB<L: LatGraph> {
    latgraph: Arc<L>,
    maxes: Mutex<BTreeMap<L::LID, L::Value>>,
}

impl<L: LatGraph> MemoryLatticeDB<L> {
    pub fn new(latgraph: Arc<L>) -> Self {
        MemoryLatticeDB {
            latgraph,
            maxes: Mutex::new(BTreeMap::new()),
        }
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for MemoryLatticeDB<L> {
    fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
        self.latgraph.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        self.maxes.lock().unwrap().get(&lid).cloned()
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeWriteDB<L::LID, L::Value, L::Cmp> for MemoryLatticeDB<L> {
    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String> {
        let default = self.latgraph.default(lid.clone())?;
        let current = self.clone().get_lattice_max(lid.clone()).await.unwrap_or(default.clone());
        let dep_db = Arc::new(DependencyLatticeDB::new(self.clone()));
        let (current_cmp, value_cmp) = join!(
            self.latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), current.clone()),
            self.latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), value));
        let joined = self.latgraph.clone().join(lid.clone(), current_cmp?, value_cmp?)?;
        if joined != current {
            self.maxes.lock().unwrap().insert(lid, joined);
        }
        Ok(())
    }
}
