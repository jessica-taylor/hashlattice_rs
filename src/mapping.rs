use std::collections::{BTreeSet, BTreeMap};
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

use crate::lattice::{LatGraph, LatLookup};
use crate::crypto::HashCode;

#[async_trait]
pub trait LatMapping<L: LatGraph> : Send + Sync {

    fn get_latgraph(&self) -> &L;

    async fn get_lattice_max(self: Arc<Self>, key: L::Key) -> Result<(L::Value, HashCode), String>;
}

#[async_trait]
pub trait LatMappingExt<L: LatGraph + 'static> : LatMapping<L> {

    async fn eval_lookup<T: Send + 'static>(self: Arc<Self>, lookup: LatLookup<L::Key, L::Value, T>) -> Result<(BTreeMap<L::Key, L::Value>, T), String> {
        let self2 = self.clone();
        lookup.evaluate_async(move |k| {
            let k = k.clone();
            let self2 = self.clone();
            async move { Ok(self2.clone().get_lattice_max(k.clone()).await?.0) }
        }).await
    }

    // async fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> Result<Self::Key, Self::Value, ()> {
    //     Ok(LatLookup::Done(()))
    // }

    // fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;

    // fn bottom(&self, key: &Self::Key) -> LatLookupResult<Self::Key, Self::Value, Self::Value>;

    // fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatLookupResult<Self::Key, Self::Value, LatLookup<Self::Key, Self::Value, Self::Value>> {
    //     Ok(LatLookup::Done(LatLookup::Done(value.clone())))
    // }

}

// #[async_trait]
// impl<L: LatGraph + 'static, M: LatMapping<L> + 'static> LatMappingExt<L> for M {
//     async fn dependencies(self: Arc<Self>, key: L::K) -> Result<BTreeSet<L::K>, String> {
//         let value = self.clone().get_lattice_max(key.clone()).await?;
//         self.get_latgraph().dependencies(&key, Some(&value))
//     }
// 
//     async fn join(self: Arc<Self>, key: L::K, v1: L::V, v2: L::V) -> Result<L::V, String> {
//         let mut deps = BTreeMap::new();
//         let deps1 = self.get_latgraph().dependencies(&key, Some(&v1))?;
//         let deps2 = self.get_latgraph().dependencies(&key, Some(&v2))?;
//         for dep in deps1.union(&deps2) {
//             deps.insert(dep.clone(), self.clone().get_lattice_max(dep.clone()).await?);
//         }
//         self.get_latgraph().join(&key, &v1, &v2, &deps)
//     }
// 
//     async fn autofill(self: Arc<Self>, key: L::K) -> Result<L::V, String> {
//         let mut deps = BTreeMap::new();
//         for dep in self.get_latgraph().dependencies(&key, None)? {
//             deps.insert(dep.clone(), self.clone().get_lattice_max(dep.clone()).await?);
//         }
//         self.get_latgraph().autofill(&key, &deps)
//     }
// }
// 
// struct JoinMapping<L: LatGraph, M1: LatMapping<L>, M2: LatMapping<L>> {
//     m1: Arc<M1>,
//     m2: Arc<M2>,
//     cache: Mutex<BTreeMap<L::K, L::V>>,
// }
// 
// impl<L: LatGraph, M1: LatMapping<L>, M2: LatMapping<L>> JoinMapping<L, M1, M2> {
//     pub fn new(m1: Arc<M1>, m2: Arc<M2>) -> Self {
//         JoinMapping { m1, m2, cache: Mutex::new(BTreeMap::new()) }
//     }
// }
// 
// #[async_trait]
// impl<L: LatGraph + 'static, M1: LatMapping<L>, M2: LatMapping<L>> LatMapping<L> for JoinMapping<L, M1, M2> {
//     fn get_latgraph(&self) -> &L {
//         self.m1.get_latgraph()
//     }
// 
//     async fn get_lattice_max(self: Arc<Self>, key: L::K) -> Result<L::V, String> {
//         {
//             let cache = self.cache.lock().unwrap();
//             if let Some(v) = cache.get(&key) {
//                 return Ok(v.clone());
//             }
//         }
//         let v1 = self.m1.clone().get_lattice_max(key.clone()).await?;
//         let v2 = self.m2.clone().get_lattice_max(key.clone()).await?;
//         let deps1 = self.get_latgraph().dependencies(&key, Some(&v1))?;
//         let deps2 = self.get_latgraph().dependencies(&key, Some(&v2))?;
//         let mut depvals = BTreeMap::new();
//         for dep in deps1.union(&deps2) {
//             depvals.insert(dep.clone(), self.clone().get_lattice_max(dep.clone()).await?);
//         }
//         let res = self.get_latgraph().join(&key, &v1, &v2, &depvals)?;
//         let mut cache = self.cache.lock().unwrap();
//         cache.insert(key, res.clone());
//         Ok(res)
//     }
// }

// pub struct MapLatticeReadDB<L: LatGraph> {
//     latgraph: Arc<L>,
//     values: Arc<BTreeMap<L::LID, L::Value>>,
// }
// 
// impl<L: LatGraph> MapLatticeReadDB<L> {
//     pub fn new(latgraph: Arc<L>, values: BTreeMap<L::LID, L::Value>) -> Self {
//         Self {
//             latgraph,
//             values: Arc::new(values)
//         }
//     }
// }
// 
// #[async_trait]
// impl<L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for MapLatticeReadDB<L> {
//     fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
//         self.latgraph.clone()
//     }
// 
//     async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Result<L::Value, String> {
//         match self.values.get(&lid) {
//             Some(v) => Ok(v.clone()),
//             None => self.latgraph.default(lid)
//         }
//     }
// }
//

// struct SerializeLatticeReadDB<L: LatGraph> {
//     db: Arc<dyn LatticeReadDB<Vec<u8>, Vec<u8>, L::Cmp>>,
//     latgraph: Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>>,
// }
// 
// #[async_trait]
// impl <L: LatGraph + 'static> LatticeReadDB<L::LID, L::Value, L::Cmp> for SerializeLatticeReadDB<L> {
//     fn get_latgraph(&self) -> Arc<dyn LatGraph<LID = L::LID, Value = L::Value, Cmp = L::Cmp>> {
//         self.latgraph.clone()
//     }
//     async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Result<L::Value, String> {
//         let ser_lid = rmp_serde::to_vec_named(&lid).unwrap();
//         let max = self.db.clone().get_lattice_max(ser_lid).await?;
//         rmp_serde::from_slice(&max).map_err(|e| e.to_string())
//     }
// }
