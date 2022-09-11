use std::collections::{BTreeMap, BTreeSet};
use async_mutex::Mutex as AsyncMutex;
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

pub struct MemoryLatticeDB<L: LatGraph> {
    latgraph: Arc<L>,
    maxes: Mutex<BTreeMap<L::LID, L::Value>>,
    dependencies: Mutex<BTreeMap<L::LID, BTreeSet<L::LID>>>,
    dependents: Mutex<BTreeMap<L::LID, BTreeSet<L::LID>>>,
    dirty: Mutex<BTreeSet<L::LID>>,

}

impl<L: LatGraph + 'static> MemoryLatticeDB<L> {
    pub fn new(latgraph: Arc<L>) -> Self {
        MemoryLatticeDB {
            latgraph,
            maxes: Mutex::new(BTreeMap::new()),
            dependencies: Mutex::new(BTreeMap::new()),
            dependents: Mutex::new(BTreeMap::new()),
            dirty: Mutex::new(BTreeSet::new())
        }
    }
    async fn update_dependencies(self: Arc<Self>, lid: L::LID) -> Result<(), String> {
        let empty_set = BTreeSet::new();
        let old_deps = self.dependencies.lock().unwrap().get(&lid).clone().unwrap_or(&empty_set).clone();
        let dep_db = Arc::new(DependencyLatticeDB::new(self.clone()));
        let val = self.clone().get_lattice_max(lid.clone()).await?;
        let _cmp = self.latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), val).await?;
        let new_deps: BTreeSet<L::LID> = dep_db.deps().keys().map(|k| k.clone()).collect();
        self.dependencies.lock().unwrap().insert(lid.clone(), new_deps.clone());
        let mut dependents = self.dependents.lock().unwrap();
        for old_dep in &old_deps {
            if !new_deps.contains(old_dep) {
                if let Some(ds) = dependents.get_mut(old_dep) {
                    ds.remove(&lid);
                }
            }
        }
        for new_dep in new_deps {
            if !old_deps.contains(&new_dep) {
                dependents.entry(new_dep).or_insert(BTreeSet::new()).insert(lid.clone());
            }
        }
        Ok(())
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for MemoryLatticeDB<L> {
    fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
        self.latgraph.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Result<L::Value, String> {
        match self.maxes.lock().unwrap().get(&lid) {
            None => self.latgraph.default(lid),
            Some(x) => Ok(x.clone())
        }
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatticeWriteDB<L::LID, L::Value, L::Cmp> for MemoryLatticeDB<L> {
    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String> {
        // maybe we do the following:
        // get deps for value, current
        // if join changed from current:
        //   update deps of value
        //   put default in things depending on current deps
        //   set pins to: pins of value + pins of dependents (pin can be bigint!)
        //   maybe instead of bigint, pin is a set of pinned lids?
        //   actually...delay recomputing pins to a pin step that deletes unpinned data
        //   wait! is it more efficient to interleave merge steps with dep-update steps???
        let default = self.latgraph.default(lid.clone())?;
        let current = self.clone().get_lattice_max(lid.clone()).await.unwrap_or(default.clone());
        let (current_cmp, value_cmp) = join!(
            self.latgraph.clone().get_comparable(self.clone(), lid.clone(), current.clone()),
            self.latgraph.clone().get_comparable(self.clone(), lid.clone(), value));
        let joined = self.latgraph.clone().join(lid.clone(), current_cmp?, value_cmp?)?;
        if joined != current {
            self.dirty.lock().unwrap().insert(lid.clone());
            self.maxes.lock().unwrap().insert(lid, joined);
        }
        Ok(())
    }
}
