use std::sync::{Arc, Mutex};
use std::collections::BTreeSet;

use futures::join;
use async_trait::async_trait;

use super::lattice::{LatGraph, LatticeReadDB, LatticeWriteDB, DependencyLatticeDB};

pub trait LatticeRawMappingDB<K, V> {
    fn get_lattice_max(&self, key: &K) -> Result<Option<V>, String>;
    fn set_lattice_max(&mut self, key: &K, value: Option<V>, deps: BTreeSet<K>) -> Result<(), String>;

    fn is_dirty(&self, key: &K) -> Result<bool, String>;
    fn set_dirty(&mut self, key: &K) -> Result<(), String>;
    fn set_undirty(&mut self, key: &K) -> Result<(), String>;
    fn get_some_dirty(&mut self) -> Result<Option<LID>, String>;

    fn get_dependencies(&self, key: &K) -> Result<BTreeSet<LID>, String>;
    fn get_dependents(&self, key: &K) -> Result<BTreeSet<LID>, String>;
}

// pub struct LatticeWrapperWriteDB<L: LatGraph> {
//     latgraph: Arc<L>,
//     raw_db: Mutex<Box<dyn Send + LatticeRawWriteDB<L::LID, L::Value>>>,
// }
// 
// impl<L: LatGraph> LatticeWrapperWriteDB<L> {
//     pub fn new(latgraph: Arc<L>, raw_db: Box<dyn Send + LatticeRawWriteDB<L::LID, L::Value>>) -> Self {
//         Self {latgraph, raw_db: Mutex::new(raw_db)}
//     }
// }
// 
// #[async_trait]
// impl<L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for LatticeWrapperWriteDB<L> {
//     fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
//         self.latgraph.clone()
//     }
//     async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Result<L::Value, String> {
//         match self.raw_db.lock().unwrap().get_lattice_max(&lid)? {
//             None => self.latgraph.default(lid),
//             Some(x) => Ok(x)
//         }
//     }
// }
// 
// #[async_trait]
// impl<L: LatGraph + 'static> LatticeWriteDB<L::LID, L::Value, L::Cmp> for LatticeWrapperWriteDB<L> {
//     async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<bool, String> {
//         let default = self.latgraph.default(lid.clone())?;
//         let current = self.clone().get_lattice_max(lid.clone()).await?;
//         // TODO: should we do a lock or something?
//         let old_dep_db = Arc::new(DependencyLatticeDB::new(self.clone()));
//         let (current_cmp, value_cmp) = join!(
//             self.latgraph.clone().get_comparable(old_dep_db.clone(), lid.clone(), current.clone()),
//             self.latgraph.clone().get_comparable(self.clone(), lid.clone(), value));
//         let joined = self.latgraph.clone().join(lid.clone(), current_cmp?, value_cmp?)?;
//         if joined != current {
//             let joined_deps: BTreeSet<L::LID> = {
//                 let dep_db = Arc::new(DependencyLatticeDB::new(self.clone()));
//                 self.latgraph.clone().get_comparable(dep_db.clone(), lid.clone(), joined.clone()).await?;
//                 dep_db.deps().keys().cloned().collect()
//             };
//             let old_deps: BTreeSet<L::LID> = old_dep_db.deps().keys().cloned().collect();
//             let mut db = self.raw_db.lock().unwrap();
//             db.set_lattice_max(&lid, if joined == default {None} else {Some(joined)})?;
//             db.set_dependencies(&lid, joined_deps.clone())?;
//             for dep in &joined_deps {
//                 if !old_deps.contains(dep) {
//                     db.add_dependent(dep, &lid)?;
//                 }
//             }
//             for dep in &old_deps {
//                 if !joined_deps.contains(dep) {
//                     db.remove_dependent(dep, &lid)?;
//                 }
//             }
//             for dep_on_val in db.get_dependents(&lid)? {
//                 db.set_dirty(&dep_on_val)?;
//             }
//             db.set_undirty(&lid)?;
//             Ok(true)
//         } else {
//             Ok(false)
//         }
//     }
// }


