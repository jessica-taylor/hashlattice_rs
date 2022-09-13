use std::collections::{BTreeMap, BTreeSet};
use async_mutex::Mutex as AsyncMutex;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use async_recursion::async_recursion;
use futures::{join, future::{join_all, try_join_all}};
use std::mem::swap;

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
// this is a monad or something... the recursion happens _when getting comparators_!
// basically, we make a MergeLatticeReadDB, which is a wrapper around two LatticeReadDBs

pub struct MergeLatticeReadDB<L: LatGraph + 'static> {
    latgraph: Arc<L>,
    db1: Arc<dyn LatticeWriteDB<L::LID, L::Value, L::Cmp>>,
    db2: Arc<dyn LatticeWriteDB<L::LID, L::Value, L::Cmp>>,
    mutexes: Mutex<BTreeMap<L::LID, Arc<AsyncMutex<()>>>>,
}

impl<L: LatGraph + 'static> MergeLatticeReadDB<L> {
    pub fn new(
        latgraph: Arc<L>,
        db1: Arc<dyn LatticeWriteDB<L::LID, L::Value, L::Cmp>>,
        db2: Arc<dyn LatticeWriteDB<L::LID, L::Value, L::Cmp>>) -> Self {
        Self {
            latgraph, db1, db2, mutexes: Mutex::new(BTreeMap::new())
        }
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for MergeLatticeReadDB<L> {
    fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
        self.latgraph.clone()
    }

    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Result<L::Value, String> {
        let mutex = self.mutexes.lock().unwrap().entry(lid.clone()).or_insert(Arc::new(AsyncMutex::new(()))).clone();
        let lock = mutex.lock().await;
        let default = self.latgraph.default(lid.clone())?;
        let (v1, v2) = join!(self.db1.clone().get_lattice_max(lid.clone()), self.db2.clone().get_lattice_max(lid.clone()));
        let v1 = v1.unwrap_or_else(|_| default.clone());
        let v2 = v2.unwrap_or_else(|_| default.clone());
        if v1 == v2 {
            return Ok(v1);
        }
        let (c1, c2) = join!(self.latgraph.clone().get_comparable(self.clone(), lid.clone(), v1.clone()),
                             self.latgraph.clone().get_comparable(self.clone(), lid.clone(), v2.clone()));
        let c1 = c1?;
        let c2 = c2?;
        let joined = self.latgraph.join(lid.clone(), c1, c2)?;
        let (res1, res2) = join!(self.db1.clone().put_lattice_value(lid.clone(), joined.clone()),
                                 self.db2.clone().put_lattice_value(lid.clone(), joined.clone()));
        res1?;
        res2?;
        Ok(joined)
    }
}
