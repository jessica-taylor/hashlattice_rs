use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::marker::PhantomData;
use serde::{Serialize, de::DeserializeOwned};
use async_trait::async_trait;

#[async_trait]
pub trait LatGraph : Send + Sync {

    type LID : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    type Value : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    type Cmp :  Clone + Send + Sync;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String>;

    async fn get_comparer(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self::LID, Self::Value, Self::Cmp>>, lid: Self::LID, value: Self::Value) -> Result<Self::Cmp, String>;

    async fn join(self: Arc<Self>, lid: Self::LID, acmp: Self::Cmp, bcmp: Self::Cmp) -> Result<Self::Value, String>;
}

#[async_trait]
pub trait LatticeReadDB<LID, Value, Cmp> : Send + Sync {

    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value, Cmp = Cmp>>;

    async fn get_lattice_max(self: Arc<Self>, lid: LID) -> Option<Value>;
}

#[async_trait]
pub trait LatticeWriteDB<LID, Value, Cmp> : LatticeReadDB<LID, Value, Cmp> {

    async fn pin_lattice(self: Arc<Self>, lid: LID) -> Result<(), String>;

    async fn put_lattice_value(self: Arc<Self>, lid: LID, value: Value) -> Result<(), String>;

    async fn unpin_lattice(self: Arc<Self>, lid: LID) -> Result<(), String>;
}

pub struct DependencyLatticeDB<LID, Value, Cmp, D: LatticeReadDB<LID, Value, Cmp>> {
    db: Arc<D>,
    deps: Mutex<BTreeSet<LID>>,
    phantom_v: PhantomData<Value>,
    phantom_c: PhantomData<Cmp>,
}

impl <LID: Send + Sync + Clone + 'static,
      Value: Send + Sync + Clone + 'static,
      Cmp,
      D: LatticeReadDB<LID, Value, Cmp>
     > DependencyLatticeDB<LID, Value, Cmp, D> {
    pub fn new(db: Arc<D>) -> Self {
        DependencyLatticeDB {
            db,
            deps: Mutex::new(BTreeSet::new()),
            phantom_v: PhantomData,
            phantom_c: PhantomData,
        }
    }
    pub fn deps(&self) -> BTreeSet<LID> {
        self.deps.lock().unwrap().clone()
    }
}

#[async_trait]
impl<LID : Send + Sync + Eq + Ord + Clone + 'static,
     Value : Send + Sync + Eq + Clone + 'static,
     Cmp: Send + Sync,
     D: LatticeReadDB<LID, Value, Cmp> + 'static
    > LatticeReadDB<LID, Value, Cmp> for DependencyLatticeDB<LID, Value, Cmp, D> {
    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value, Cmp = Cmp>> {
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

    type Cmp = L::Cmp;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        Ok(rmp_serde::to_vec_named(&self.0.default(lid)?).unwrap())
    }

    async fn get_comparer(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self::LID, Self::Value, L::Cmp>>, lid: Self::LID, value: Self::Value) -> Result<L::Cmp, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let value = rmp_serde::from_slice(&value).map_err(|x| x.to_string())?;
        let db = Arc::new(SerializeLatticeReadDB { db, lattice: self.0.clone() });
        self.0.clone().get_comparer(db, lid, value).await
    }

    async fn join(self: Arc<Self>, lid: Self::LID, acmp: L::Cmp, bcmp: L::Cmp) -> Result<Self::Value, String> {
        let lid: L::LID = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        Ok(rmp_serde::to_vec_named(&self.0.clone().join(lid, acmp, bcmp).await?).unwrap())
    }
}

struct SerializeLatticeReadDB<LID, Value, Cmp> {
    db: Arc<dyn LatticeReadDB<Vec<u8>, Vec<u8>, Cmp>>,
    lattice: Arc<dyn LatGraph<LID = LID, Value = Value, Cmp = Cmp>>,
}

#[async_trait]
impl <LID: 'static + Serialize + DeserializeOwned + Send + Sync,
      Value: 'static + Serialize + DeserializeOwned + Send + Sync,
      Cmp
     > LatticeReadDB<LID, Value, Cmp> for SerializeLatticeReadDB<LID, Value, Cmp> {
    fn get_lattice(&self) -> Arc<dyn LatGraph<LID = LID, Value = Value, Cmp = Cmp>> {
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

pub struct EnumLatGraph<LID: IsEnum, Value: IsEnum, Cmp, L: LatGraph<LID = LID, Value = Value, Cmp = Cmp>>(Vec<Arc<L>>);

impl<LID: IsEnum, Value: IsEnum, Cmp, L: LatGraph<LID = LID, Value = Value, Cmp = Cmp>> EnumLatGraph<LID, Value, Cmp, L> {
    pub fn new(l: Vec<Arc<L>>) -> Self {
        EnumLatGraph(l)
    }
}

#[async_trait]
impl<LID: IsEnum + Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
     Value: IsEnum + Eq + Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
     Cmp: Clone + Send + Sync,
     L: LatGraph<LID = LID, Value = Value, Cmp = Cmp> + 'static
    > LatGraph for EnumLatGraph<LID, Value, Cmp, L> {

    type LID = LID;

    type Value = Value;

    type Cmp = Cmp;

    fn default(&self, lid: LID) -> Result<L::Value, String> {
        let branch = lid.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].default(lid)
    }

    async fn get_comparer(self: Arc<Self>, db: Arc<dyn LatticeReadDB<LID, Value, Cmp>>, lid: LID, value: Value) -> Result<Cmp, String> {
        let branch = lid.get_branch();
        let branch2 = value.get_branch();
        if branch != branch2 {
            return Err(format!("branch {} != {}", branch, branch2));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        let lattice = &self.0[branch];
        lattice.clone().get_comparer(db, lid, value).await
    }

    async fn join(self: Arc<Self>, lid: LID, acmp: Cmp, bcmp: Cmp) -> Result<Value, String> {
        let branch = lid.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].clone().join(lid, acmp, bcmp).await
    }
}
