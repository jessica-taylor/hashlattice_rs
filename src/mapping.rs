use std::collections::{BTreeSet, BTreeMap};
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{LatGraph, LatLookup};
use crate::crypto::{Hash, hash};

type DepsHash<L> = Hash<BTreeMap<<L as TaggedMapping>::Key, <L as TaggedMapping>::Value>>;

#[async_trait]
pub trait LatMapping<L: LatGraph> : Send + Sync {

    fn get_latgraph(&self) -> &L;

    async fn get_lattice_max(self: Arc<Self>, key: L::Key) -> Result<(L::Value, DepsHash<L>), String>;
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

    async fn check_elem(self: Arc<Self>, key: &L::Key, value: &L::Value) -> Result<(), String> {
        Ok(self.clone().eval_lookup(self.get_latgraph().check_elem(key, value)?).await?.1)
    }

    async fn join(self: Arc<Self>, key: &L::Key, value1: &L::Value, value2: &L::Value) -> Result<L::Value, String> {
        Ok(self.clone().eval_lookup(self.get_latgraph().join(key, value1, value2)?).await?.1)
    }

    async fn bottom(self: Arc<Self>, key: &L::Key) -> Result<L::Value, String> {
        Ok(self.clone().eval_lookup(self.get_latgraph().bottom(key)?).await?.1)
    }

    async fn transport(self: Arc<Self>, key: &L::Key, value: &L::Value) -> Result<LatLookup<L::Key, L::Value, L::Value>, String> {
        Ok(self.clone().eval_lookup(self.get_latgraph().transport(key, value)?).await?.1)
    }
}

impl<L: LatGraph + 'static, M: LatMapping<L>> LatMappingExt<L> for M {}

struct JoinMapping<L: LatGraph, M1: LatMapping<L>, M2: LatMapping<L>> {
    m1: Arc<M1>,
    m2: Arc<M2>,
    cache: Mutex<BTreeMap<L::Key, (L::Value, DepsHash<L>)>>,
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

    async fn get_lattice_max(self: Arc<Self>, key: L::Key) -> Result<(L::Value, DepsHash<L>), String> {
        {
            let cache = self.cache.lock().unwrap();
            if let Some(res) = cache.get(&key) {
                return Ok(res.clone());
            }
        }
        let (v1, h1) = self.m1.clone().get_lattice_max(key.clone()).await?;
        let (v2, h2) = self.m2.clone().get_lattice_max(key.clone()).await?;
        if h1 == h2 {
            assert!(v1 == v2);
            let mut cache = self.cache.lock().unwrap();
            cache.insert(key, (v1.clone(), h1));
            return Ok((v1, h1));
        }
        let (_, tr1) = self.clone().eval_lookup(self.m1.clone().transport(&key, &v1).await?).await?;
        let (_, tr2) = self.clone().eval_lookup(self.m2.clone().transport(&key, &v2).await?).await?;
        let join = self.clone().join(&key, &tr1, &tr2).await?;
        let (join_deps, ()) = self.clone().eval_lookup(self.get_latgraph().check_elem(&key, &join)?).await?;
        let mut cache = self.cache.lock().unwrap();
        let hash_deps = hash(&join_deps);
        cache.insert(key, (join.clone(), hash_deps));
        Ok((join, hash_deps))
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
