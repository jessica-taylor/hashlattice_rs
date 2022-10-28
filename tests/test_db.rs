use hashlattice::error::{Res, str_error};
use hashlattice::tagged_mapping::TaggedMapping;
use hashlattice::lattice::{HashLookup, EmptyHashLookup, ComputationLibrary, EmptyComputationLibrary, ImmutComputationContext, MutComputationContext, LatticeLibrary, EmptyLatticeLibrary};
use hashlattice::db::{DepDB, LatStore, LatDBMapping};
use hashlattice::sql_db::SqlDepDB;

struct EmptyMapping;
impl TaggedMapping for EmptyMapping {
    type Key = ();
    type Value = ();
}

struct MaxTupleMapping;
impl TaggedMapping for MaxTupleMapping {
    type Key = String;
    type Value = Vec<usize>;
}

struct MaxTupleLatLibrary(usize);

impl LatticeLibrary<EmptyMapping, MaxTupleMapping> for MaxTupleLatLibrary {
    fn check_elem(&self, key: &String, value: &Vec<usize>, ctx: &mut dyn ImmutComputationContext<EmptyMapping>) -> Res<()> {
        if value.len() != self.0 {
            return str_error("wrong length");
        }
        Ok(())
    }
    fn join(&self, key: &String, value1: &Vec<usize>, value2: &Vec<usize>, ctx: &mut dyn MutComputationContext<EmptyMapping>) -> Res<Vec<usize>> {
        let mut result = value1.clone();
        for (i, v) in value2.iter().enumerate() {
            result[i] = std::cmp::max(result[i], *v);
        }
        Ok(result)
    }

}


#[tokio::test]
async fn test_db() {
    let db = SqlDepDB::<LatDBMapping<EmptyMapping, MaxTupleMapping>>::new(":memory:").unwrap();
    db.initialize().unwrap();
    let store = LatStore::new(db, EmptyComputationLibrary, MaxTupleLatLibrary(3), EmptyHashLookup);
}
