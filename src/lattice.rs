use std::collections::{BTreeSet, BTreeMap};
use std::sync::{Arc, Mutex};
use std::marker::PhantomData;
use serde::{Serialize, de::DeserializeOwned};
use async_trait::async_trait;

/// A graph where each item is a semilattice, which may depend on other lattice max values.
pub trait LatGraph : Send + Sync {

    /// Keys identifying lattice value keys.
    type K : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    /// The values themselves.
    type V : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    /// Dependencies of a given key.
    fn dependencies(&self, key: &Self::K, value: &Self::V) -> Result<BTreeSet<Self::K>, String>;

    /// Joins two values given dependencies.
    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String>;

    /// The default element of the lattice.
    fn default(&self, key: &Self::K) -> Result<Self::V, String>;
}

#[async_trait]
pub trait LatticeSpec<K, V> : Send + Sync {

    fn get_latgraph(&self) -> Arc<dyn LatGraph<K = K, V = V>>;

    async fn get_lattice_max(self: Arc<Self>, key: K) -> Result<V, String>;
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

pub struct SerializeLatGraph<L: LatGraph>(Arc<L>);

impl<L: LatGraph> SerializeLatGraph<L> {
    pub fn new(l: Arc<L>) -> Self {
        SerializeLatGraph(l)
    }
}

impl<L: LatGraph + 'static> LatGraph for SerializeLatGraph<L> {

    type K = Vec<u8>;

    type V = Vec<u8>;

    fn dependencies(&self, key: &Vec<u8>, value: &Vec<u8>) -> Result<BTreeSet<Vec<u8>>, String> {
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let value = rmp_serde::from_slice(value).map_err(|e| format!("failed to deserialize value: {}", e))?;
        let mut deps = BTreeSet::new();
        for dep in self.0.dependencies(&key, &value)? {
            deps.insert(rmp_serde::to_vec(&dep).map_err(|e| format!("failed to serialize key: {}", e))?);
        }
        Ok(deps)
    }

    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let mut deps2 = BTreeMap::new();
        for (k, v) in deps.into_iter() {
            let k = rmp_serde::from_slice(&k).map_err(|e| format!("failed to deserialize key: {}", e))?;
            let v = rmp_serde::from_slice(&v).map_err(|e| format!("failed to deserialize value: {}", e))?;
            deps2.insert(k, v);
        }
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let v1 = rmp_serde::from_slice(v1).map_err(|e| format!("failed to deserialize value: {}", e))?;
        let v2 = rmp_serde::from_slice(v2).map_err(|e| format!("failed to deserialize value: {}", e))?;
        let v = self.0.join(&key, &v1, &v2, &deps2)?;
        rmp_serde::to_vec_named(&v).map_err(|e| format!("failed to serialize value: {}", e))
    }

    fn default(&self, key: &Self::K) -> Result<Self::V, String> {
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let v = self.0.default(&key)?;
        rmp_serde::to_vec_named(&v).map_err(|e| format!("failed to serialize value: {}", e))
    }
}

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

pub trait IsEnum {
    fn get_branch(&self) -> usize;
}

pub struct EnumLatGraph<L: LatGraph>(Vec<Arc<L>>);

impl<L: LatGraph> EnumLatGraph<L> {
    pub fn new(l: Vec<Arc<L>>) -> Self {
        EnumLatGraph(l)
    }
}

impl<L: LatGraph + 'static> LatGraph for EnumLatGraph<L>
where L::K: IsEnum, L::V: IsEnum {
    
    type K = L::K;

    type V = L::V;

    fn dependencies(&self, key: &Self::K, value: &Self::V) -> Result<BTreeSet<Self::K>, String> {
        let branch = key.get_branch();
        let branch2 = value.get_branch();
        if branch != branch2 {
            return Err(format!("key and value have different branches: {} vs {}", branch, branch2));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].dependencies(key, value)
    }

    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let branch = key.get_branch();
        let branch2 = v1.get_branch();
        let branch3 = v2.get_branch();
        if branch != branch2 || branch != branch3 {
            return Err(format!("key and value have different branches: {} vs {} vs {}", branch, branch2, branch3));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].join(key, v1, v2, deps)
    }

    fn default(&self, key: &Self::K) -> Result<Self::V, String> {
        let branch = key.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].default(key)
    }

}
