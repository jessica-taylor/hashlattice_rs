use std::collections::{BTreeSet, BTreeMap};
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

use super::lattice::LatGraph;

#[async_trait]
pub trait LatMapping<L: LatGraph> : Send + Sync {

    fn get_latgraph(&self) -> &L;

    async fn get_lattice_max(self: Arc<Self>, key: L::K) -> Result<L::V, String>;
}

struct JoinMapping<L: LatGraph, M1: LatMapping<L>, M2: LatMapping<L>> {
    m1: Arc<M1>,
    m2: Arc<M2>,
    cache: Mutex<BTreeMap<L::K, L::V>>,
}

impl<L: LatGraph, M1: LatMapping<L>, M2: LatMapping<L>> JoinMapping<L, M1, M2> {
    pub fn new(m1: Arc<M1>, m2: Arc<M2>) -> Self {
        JoinMapping { m1, m2, cache: Mutex::new(BTreeMap::new()) }
    }
}

#[async_trait]
impl<L: LatGraph + 'static, M1: LatMapping<L>, M2: LatMapping<L>> LatMapping<L> for JoinMapping<L, M1, M2> {
    fn get_latgraph(&self) -> &L {
        self.m1.get_latgraph()
    }

    async fn get_lattice_max(self: Arc<Self>, key: L::K) -> Result<L::V, String> {
        {
            let cache = self.cache.lock().unwrap();
            if let Some(v) = cache.get(&key) {
                return Ok(v.clone());
            }
        }
        let v1 = self.m1.clone().get_lattice_max(key.clone()).await?;
        let v2 = self.m2.clone().get_lattice_max(key.clone()).await?;
        let deps1 = self.get_latgraph().dependencies(&key, &v1)?;
        let deps2 = self.get_latgraph().dependencies(&key, &v2)?;
        let mut depvals = BTreeMap::new();
        for dep in deps1.union(&deps2) {
            depvals.insert(dep.clone(), self.clone().get_lattice_max(dep.clone()).await?);
        }
        let res = self.get_latgraph().join(&key, &v1, &v2, &depvals)?;
        let mut cache = self.cache.lock().unwrap();
        cache.insert(key, res.clone());
        Ok(res)
    }
}

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
