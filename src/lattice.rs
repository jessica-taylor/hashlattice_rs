use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::marker::PhantomData;
use serde::{Serialize, de::DeserializeOwned};
use async_trait::async_trait;

#[async_trait]
pub trait LatGraph : Send + Sync {

    type LID : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    type Value : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String>;

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self::LID, Self::Value>>, lid: Self::LID, value: Self::Value) -> Result<BTreeSet<Self::LID>, String>;

    async fn join(self: Arc<Self>, lid: Self::LID, deps: BTreeMap<Self::LID, Self::Value>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String>;
}

#[async_trait]
pub trait LatticeReadDB<LID, Value> : Send + Sync {

    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value>>;

    async fn get_lattice_max(self: Arc<Self>, lid: LID) -> Option<Value>;
}

#[async_trait]
pub trait LatticeWriteDB<LID, Value> : Send + Sync {

    async fn pin_lattice(self: Arc<Self>, lid: LID) -> Result<(), String>;

    async fn put_lattice_value(self: Arc<Self>, lid: LID, value: Value) -> Result<(), String>;

    async fn unpin_lattice(self: Arc<Self>, lid: LID) -> Result<(), String>;
}

pub struct DependencyLatticeDB<LID, Value, D: LatticeReadDB<LID, Value>> {
    db: Arc<D>,
    deps: Mutex<BTreeSet<LID>>,
    phantom: PhantomData<Value>,
}

impl <LID: Send + Sync + Clone + 'static, Value: Send + Sync + Clone + 'static, D: LatticeReadDB<LID, Value>> DependencyLatticeDB<LID, Value, D> {
    pub fn new(db: Arc<D>) -> Self {
        DependencyLatticeDB {
            db,
            deps: Mutex::new(BTreeSet::new()),
            phantom: PhantomData,
        }
    }
    pub fn deps(&self) -> BTreeSet<LID> {
        self.deps.lock().unwrap().clone()
    }
}

#[async_trait]
impl<LID : Send + Sync + Eq + Ord + Clone + 'static, Value : Send + Sync + Eq + Clone + 'static, D: LatticeReadDB<LID, Value> + 'static> LatticeReadDB<LID, Value> for DependencyLatticeDB<LID, Value, D> {
    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value>> {
        self.db.get_lattice()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: LID) -> Option<Value> {
        self.deps.lock().unwrap().insert(lid.clone());
        self.db.clone().get_lattice_max(lid).await
    }
}
pub struct SerializeLatGraph<L: LatGraph>(Arc<L>);

impl<L: LatGraph> SerializeLatGraph<L> {
    pub fn new(l: Arc<L>) -> Self {
        SerializeLatGraph(l)
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatGraph for SerializeLatGraph<L> {

    type LID = Vec<u8>;

    type Value = Vec<u8>;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        Ok(rmp_serde::to_vec_named(&self.0.default(lid)?).unwrap())
    }

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self::LID, Self::Value>>, lid: Self::LID, value: Self::Value) -> Result<BTreeSet<Self::LID>, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let value = rmp_serde::from_slice(&value).map_err(|x| x.to_string())?;
        let db = Arc::new(SerializeLatticeReadDB { db, lattice: self.0.clone() });
        let deps = self.0.clone().dependencies(db, lid, value).await?;
        Ok(deps.into_iter().map(|x| rmp_serde::to_vec_named(&x).unwrap()).collect())
    }

    async fn join(self: Arc<Self>, lid: Self::LID, deps: BTreeMap<Self::LID, Self::Value>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String> {
        let lid: L::LID = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let default = self.0.default(lid.clone())?;
        let a = rmp_serde::from_slice(&a).unwrap_or_else(|_| default.clone());
        let b = rmp_serde::from_slice(&b).unwrap_or(default);
        let deps = deps.into_iter().map(|(k, v)| {
            let k: L::LID = rmp_serde::from_slice(&k).unwrap();
            let v: L::Value = rmp_serde::from_slice(&v).unwrap();
            (k, v)
        }).collect();
        Ok(rmp_serde::to_vec_named(&self.0.clone().join(lid, deps, a, b).await?).unwrap())
    }
}

struct SerializeLatticeReadDB<LID, Value> {
    db: Arc<dyn LatticeReadDB<Vec<u8>, Vec<u8>>>,
    lattice: Arc<dyn LatGraph<LID = LID, Value = Value>>,
}

#[async_trait]
impl <LID: 'static + Serialize + DeserializeOwned + Send + Sync, Value: 'static + Serialize + DeserializeOwned + Send + Sync> LatticeReadDB<LID, Value> for SerializeLatticeReadDB<LID, Value> {
    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value>> {
        self.lattice.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: LID) -> Option<Value> {
        let ser_lid = rmp_serde::to_vec_named(&lid).unwrap();
        let max = self.db.clone().get_lattice_max(ser_lid).await?;
        Some(rmp_serde::from_slice(&max).unwrap())
    }
}

pub trait IsEnum {
    fn get_branch(&self) -> usize;
}

pub struct EnumLatGraph<LID: IsEnum, Value: IsEnum, L: LatGraph<LID = LID, Value = Value>>(Vec<Arc<L>>);

impl<LID: IsEnum, Value: IsEnum, L: LatGraph<LID = LID, Value = Value>> EnumLatGraph<LID, Value, L> {
    pub fn new(l: Vec<Arc<L>>) -> Self {
        EnumLatGraph(l)
    }
}

#[async_trait]
impl<LID: IsEnum + Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
     Value: IsEnum + Eq + Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
     L: LatGraph<LID = LID, Value = Value> + 'static
    > LatGraph for EnumLatGraph<LID, Value, L> {

    type LID = L::LID;

    type Value = L::Value;

    fn default(&self, lid: L::LID) -> Result<L::Value, String> {
        let branch = lid.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].default(lid)
    }

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<L::LID, L::Value>>, lid: L::LID, value: L::Value) -> Result<BTreeSet<L::LID>, String> {
        let branch = lid.get_branch();
        let branch2 = value.get_branch();
        if branch != branch2 {
            return Err(format!("branch {} != {}", branch, branch2));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        let lattice = &self.0[branch];
        lattice.clone().dependencies(db, lid, value).await
    }

    async fn join(self: Arc<Self>, lid: L::LID, deps: BTreeMap<L::LID, L::Value>, a: L::Value, b: L::Value) -> Result<L::Value, String> {
        let branch = lid.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        let lattice = &self.0[branch];
        let aval = if a.get_branch() == branch {
            a
        } else {
            lattice.default(lid.clone())?
        };
        let bval = if b.get_branch() == branch {
            b
        } else {
            lattice.default(lid.clone())?
        };
        lattice.clone().join(lid, deps, aval, bval).await
    }
}
