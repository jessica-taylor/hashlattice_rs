use std::sync::Arc;
use serde::{Serialize, de::DeserializeOwned};
use async_trait::async_trait;

#[async_trait]
pub trait Semilattice : Send + Sync {

    type LID : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    type Value : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String>;

    async fn join(self: Arc<Self>, lid: Self::LID, db: Arc<dyn LatticeReadDB<Self>>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String>;
}

#[async_trait]
pub trait LatticeReadDB<L: Semilattice> : Send + Sync {
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value>;
}

#[async_trait]
pub trait LatticeWriteDB<L: Semilattice> : LatticeReadDB<L> {

    async fn pin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String>;

    async fn put_lattice_value(self: Arc<Self>, lid: L::LID, value: L::Value) -> Result<(), String>;

    async fn unpin_lattice(self: Arc<Self>, lid: L::LID) -> Result<(), String>;
}

pub struct SerializeSemilattice<L: Semilattice>(Arc<L>);

impl<L: Semilattice> SerializeSemilattice<L> {
    pub fn new(l: Arc<L>) -> Self {
        SerializeSemilattice(l)
    }
}

#[async_trait]
impl<L: Semilattice + 'static> Semilattice for SerializeSemilattice<L> {

    type LID = Vec<u8>;

    type Value = Vec<u8>;

    fn default(&self, lid: Self::LID) -> Result<Self::Value, String> {
        let lid = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        Ok(rmp_serde::to_vec_named(&self.0.default(lid)?).unwrap())
    }

    async fn join(self: Arc<Self>, lid: Self::LID, db: Arc<dyn LatticeReadDB<Self>>, a: Self::Value, b: Self::Value) -> Result<Self::Value, String> {
        let lid: L::LID = rmp_serde::from_slice(&lid).map_err(|x| x.to_string())?;
        let default = self.0.default(lid.clone())?;
        let a = rmp_serde::from_slice(&a).unwrap_or(default.clone());
        let b = rmp_serde::from_slice(&b).unwrap_or(default);
        let db = Arc::new(SerializeLatticeReadDB(db));
        Ok(rmp_serde::to_vec_named(&self.0.clone().join(lid, db, a, b).await?).unwrap())
    }
}

struct SerializeLatticeReadDB<L: Semilattice>(Arc<dyn LatticeReadDB<SerializeSemilattice<L>>>);

#[async_trait]
impl <L: Semilattice + 'static> LatticeReadDB<L> for SerializeLatticeReadDB<L> {
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        let ser_lid = rmp_serde::to_vec_named(&lid).unwrap();
        let max = self.0.clone().get_lattice_max(ser_lid).await?;
        Some(rmp_serde::from_slice(&max).unwrap())
    }
}

pub struct EnumSemilattice<L: Semilattice>(Vec<Arc<L>>);

impl<L: Semilattice> EnumSemilattice<L> {
    pub fn new(l: Vec<Arc<L>>) -> Self {
        EnumSemilattice(l)
    }
}

#[async_trait]
impl<L: Semilattice + 'static> Semilattice for EnumSemilattice<L> {

    type LID = (usize, L::LID);

    type Value = (usize, L::Value);

    fn default(&self, (branch, lid): Self::LID) -> Result<Self::Value, String> {
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        Ok((branch, self.0[branch].default(lid)?))
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
        let db = Arc::new(EnumLatticeReadDB {db, branch});
        Ok((branch, lattice.clone().join(lid, db, aval, bval).await?))
    }
}

struct EnumLatticeReadDB<L: Semilattice> {
    db: Arc<dyn LatticeReadDB<EnumSemilattice<L>>>,
    branch: usize,
}

#[async_trait]
impl <L: Semilattice + 'static> LatticeReadDB<L> for EnumLatticeReadDB<L> {
    async fn get_lattice_max(self: Arc<Self>, lid: L::LID) -> Option<L::Value> {
        let (max_branch, max_v) = self.db.clone().get_lattice_max((self.branch, lid)).await?;
        if max_branch != self.branch {
            panic!("max branch {} != {}", max_branch, self.branch);
        }
        Some(max_v)
    }
}

