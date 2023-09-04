
use std::sync::{Arc, Mutex, Weak};

struct CellUpdater {
    dirty: bool,
    dependents: Vec<Weak<Mutex<CellUpdater>>>,
    refresh_fn: Box<dyn FnMut() -> Result<(), String>>
}

impl CellUpdater {
    fn new<F : FnMut() -> Result<(), String> + 'static>(f: F) -> CellUpdater {
        Self {
            dirty: false,
            refresh_fn: Box::new(f),
            dependents: Vec::new()
        }
    }
    fn value_changed(&mut self) {
        if !self.dirty {
            self.dirty = true;
            let mut new_deps = Vec::new();
            for dep in &self.dependents {
                if let Some(dep_arc) = dep.upgrade() {
                    dep_arc.lock().unwrap().value_changed();
                    new_deps.push(Arc::downgrade(&dep_arc));
                }
            }
            self.dependents = new_deps;
        }
    }
    fn add_dependent(&mut self, dep: &Arc<Mutex<CellUpdater>>) {
        self.dependents.push(Arc::downgrade(dep));
        dep.lock().unwrap().value_changed();
    }
    fn refresh(&mut self) -> Result<(), String> {
        if self.dirty {
            (self.refresh_fn)()?;
            self.dirty = false;
        }
        Ok(())
    }
}

struct DataCell<T> {
    updater: Arc<Mutex<CellUpdater>>,
    value: T,
    update_fn: Box<dyn FnMut() -> Result<T, String>>,
}

impl<T : Clone + 'static> DataCell<T> {
    fn new<F : FnMut() -> Result<T, String> + 'static>(mut update_fn: F) -> Result<Arc<Mutex<Self>>, String> {
        let initial_value = update_fn()?;
        let this = Arc::new(Mutex::new(Self {
            updater: Arc::new(Mutex::new(CellUpdater::new(|| Ok(())))),
            value: initial_value,
            update_fn: Box::new(update_fn)
        }));
        let this2 = this.clone();
        let updater = CellUpdater::new(move || {
            let mut this_lock = this2.lock().unwrap();
            let new_val = (this_lock.update_fn)()?;
            this_lock.value = new_val;
            Ok(())
        });
        this.lock().unwrap().updater = Arc::new(Mutex::new(updater));
        Ok(this)
    }
    fn get_value(&self) -> Result<T, String> {
        self.updater.lock().unwrap().refresh()?;
        Ok(self.value.clone())
    }
}
