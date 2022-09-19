use std::sync::Arc;
use std::collections::{BTreeSet, BTreeMap};
use std::marker::PhantomData;

use async_trait::async_trait;

use serde::{Serialize, de::DeserializeOwned};

/// A graph where each item is a semilattice, which may depend on other lattice max values.
#[async_trait]
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
    async fn autofill(&self, key: &Self::K, vals: Arc<dyn AutofillDatabase<Self::K, Self::V>>) -> Result<Self::V, String>;
}

#[async_trait]
pub trait AutofillDatabase<K, V> : Send + Sync {
    async fn get_value(self: Arc<Self>, keys: Vec<K>) -> Result<V, String>;
}



pub struct SerializeLatGraph<'a, L: LatGraph>(&'a L);

impl<'a, L: LatGraph> SerializeLatGraph<'a, L> {
    pub fn new(l: &'a L) -> Self {
        SerializeLatGraph(l)
    }
}

#[async_trait]
impl<'a, L: LatGraph + 'static> LatGraph for SerializeLatGraph<'a, L> {

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

    async fn autofill(&self, key: &Self::K, vals: Arc<dyn AutofillDatabase<Self::K, Self::V>>) -> Result<Self::V, String> {
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let v = self.0.autofill(&key, Arc::new(SerializeAutofillDatabase::<L>::new(vals))).await?;
        rmp_serde::to_vec_named(&v).map_err(|e| format!("failed to serialize value: {}", e))
    }
}

struct SerializeAutofillDatabase<L: LatGraph> {
    db: Arc<dyn AutofillDatabase<Vec<u8>, Vec<u8>>>,
    _phantom: std::marker::PhantomData<L>,
}

impl<L: LatGraph> SerializeAutofillDatabase<L> {
    fn new(db: Arc<dyn AutofillDatabase<Vec<u8>, Vec<u8>>>) -> Self {
        SerializeAutofillDatabase {db, _phantom: PhantomData}
    }
}

#[async_trait]
impl<L: LatGraph> AutofillDatabase<L::K, L::V> for SerializeAutofillDatabase<L> {
    async fn get_value(self: Arc<Self>, keys: Vec<L::K>) -> Result<L::V, String> {
        let mut ks = Vec::new();
        for k in keys {
            ks.push(rmp_serde::to_vec(&k).map_err(|e| format!("failed to serialize key: {}", e))?);
        }
        let res = self.db.clone().get_value(ks).await?;
        rmp_serde::from_slice(&res).map_err(|e| format!("failed to deserialize value: {}", e))
    }
}

pub trait IsEnum {
    fn get_branch(&self) -> usize;
}

pub struct EnumLatGraph<'a, L: LatGraph>(Vec<&'a L>);

impl<'a, L: LatGraph> EnumLatGraph<'a, L> {
    pub fn new(l: Vec<&'a L>) -> Self {
        EnumLatGraph(l)
    }
}

#[async_trait]
impl<'a, L: LatGraph + 'static> LatGraph for EnumLatGraph<'a, L>
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

    async fn autofill(&self, key: &Self::K, vals: Arc<dyn AutofillDatabase<Self::K, Self::V>>) -> Result<Self::V, String> {
        let branch = key.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].autofill(key, vals).await
    }
}
