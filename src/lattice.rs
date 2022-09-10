use std::sync::Arc;
use serde::{Serialize, de::DeserializeOwned};
use async_trait::async_trait;

#[async_trait]
pub trait LatGraph : Send + Sync {

    type LID : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    type Value : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String>;

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self>>, lid: Self::LID, value: Self::Value) -> Result<Vec<Self::LID>, String>;

    async fn join(self: Arc<Self>, lid: Self::LID, db: Arc<dyn LatticeReadDB<Self>>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String>;
}

#[async_trait]
pub trait LatticeReadDB<L: LatGraph> : Send + Sync {

    fn get_lattice(&self) -> Arc<L>;

    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value>;
}

#[async_trait]
pub trait LatticeWriteDB<L: LatGraph> : LatticeReadDB<L> {

    async fn pin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String>;

    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String>;

    async fn unpin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String>;
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

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self>>, lid: Self::LID, value: Self::Value) -> Result<Vec<Self::LID>, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let value = rmp_serde::from_slice(&value).map_err(|x| x.to_string())?;
        let db = Arc::new(SerializeLatticeReadDB { db, lattice: self.0.clone() });
        let deps = self.0.clone().dependencies(db, lid, value).await?;
        Ok(deps.into_iter().map(|x| rmp_serde::to_vec_named(&x).unwrap()).collect())
    }

    async fn join(self: Arc<Self>, lid: Self::LID, db: Arc<dyn LatticeReadDB<Self>>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String> {
        let lid: L::LID = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let default = self.0.default(lid.clone())?;
        let a = rmp_serde::from_slice(&a).unwrap_or_else(|_| default.clone());
        let b = rmp_serde::from_slice(&b).unwrap_or(default);
        let db = Arc::new(SerializeLatticeReadDB { db, lattice: self.0.clone() });
        Ok(rmp_serde::to_vec_named(&self.0.clone().join(lid, db, a, b).await?).unwrap())
    }
}

struct SerializeLatticeReadDB<L: LatGraph> {
    db: Arc<dyn LatticeReadDB<SerializeLatGraph<L>>>,
    lattice: Arc<L>,
}

#[async_trait]
impl <L: LatGraph + 'static> LatticeReadDB<L> for SerializeLatticeReadDB<L> {
    fn get_lattice(&self) -> Arc<L> {
        self.lattice.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        let ser_lid = rmp_serde::to_vec_named(&lid).unwrap();
        let max = self.db.clone().get_lattice_max(ser_lid).await?;
        Some(rmp_serde::from_slice(&max).unwrap())
    }
}

pub struct EnumLatGraph<L: LatGraph>(Vec<Arc<L>>);

impl<L: LatGraph> EnumLatGraph<L> {
    pub fn new(l: Vec<Arc<L>>) -> Self {
        EnumLatGraph(l)
    }
}

#[async_trait]
impl<L: LatGraph + 'static> LatGraph for EnumLatGraph<L> {

    type LID = (usize, L::LID);

    type Value = (usize, L::Value);

    fn default(&self, (branch, lid): Self::LID) -> Result<Self::Value, String> {
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        Ok((branch, self.0[branch].default(lid)?))
    }

    async fn dependencies(self: Arc<Self>, db: Arc<dyn LatticeReadDB<Self>>, (branch, lid): Self::LID, (branch2, value): Self::Value) -> Result<Vec<Self::LID>, String> {
        if branch != branch2 {
            return Err(format!("branch {} != {}", branch, branch2));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        let lattice = &self.0[branch];
        let db = Arc::new(EnumLatticeReadDB {db, branch, lattice: lattice.clone()});
        let deps = lattice.clone().dependencies(db, lid, value).await?;
        Ok(deps.into_iter().map(|x| (branch, x)).collect())
    }

    async fn join(self: Arc<Self>, (branch, lid): Self::LID, db: Arc<dyn LatticeReadDB<Self>>, (a_branch, a): Self::Value, (b_branch, b): Self::Value) -> Result<Self::Value, String> {
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        let lattice = &self.0[branch];
        let aval = if a_branch == branch {
            a
        } else {
            lattice.default(lid.clone())?
        };
        let bval = if b_branch == branch {
            b
        } else {
            lattice.default(lid.clone())?
        };
        let db = Arc::new(EnumLatticeReadDB {db, branch, lattice: lattice.clone()});
        Ok((branch, lattice.clone().join(lid, db, aval, bval).await?))
    }
}

struct EnumLatticeReadDB<L: LatGraph> {
    branch: usize,
    db: Arc<dyn LatticeReadDB<EnumLatGraph<L>>>,
    lattice: Arc<L>,
}

#[async_trait]
impl <L: LatGraph + 'static> LatticeReadDB<L> for EnumLatticeReadDB<L> {
    fn get_lattice(&self) -> Arc<L> {
        self.lattice.clone()
    }
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        let (max_branch, max_v) = self.db.clone().get_lattice_max((self.branch, lid)).await?;
        if max_branch != self.branch {
            panic!("max branch {} != {}", max_branch, self.branch);
        }
        Some(max_v)
    }
}

