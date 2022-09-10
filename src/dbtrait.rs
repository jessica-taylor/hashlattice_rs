

trait LatticeDB<LID: Eq + Ord + Clone, T: Eq + Clone> : LatticeMap<LID, T> {
    fn get_lattice_max(&self, lid: LID) -> Option<&T>;
    // note: this is going to query the lattice DB!
    fn put_lattice_value(&self, lid: LID, value: T) -> Result<(), String>;
}
