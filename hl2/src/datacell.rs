
use std::sync::{Arc, Mutex, Weak};

struct CellUpdater {
    dirty: bool,
    dependents: Vec<Weak<Mutex<CellUpdater>>>,
    refresh_fn: Box<dyn FnMut() -> Result<(), String>>
}

impl CellUpdater {
    fn new<F : FnMut() -> Result<(), String> + 'static>(f: F) -> CellUpdater {
        Self {
            dirty: true,
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
    value: Mutex<T>,
    update_fn: Mutex<Box<dyn FnMut() -> Result<T, String>>>,
}

impl<T : Clone + 'static> DataCell<T> {
    fn new<F : FnMut() -> Result<T, String> + 'static>(value: T, update_fn: F) -> Arc<Mutex<Self>> {
        let this = Arc::new(Mutex::new(Self {
            updater: Arc::new(Mutex::new(CellUpdater::new(|| Ok(())))),
            value: Mutex::new(value),
            update_fn: Mutex::new(Box::new(update_fn))
        }));
        let this2 = this.clone();
        let updater = CellUpdater::new(move || {
            let this_lock = this2.lock().unwrap();
            let new_val = (this_lock.update_fn.lock().unwrap())()?;
            *this_lock.value.lock().unwrap() = new_val;
            Ok(())
        });
        this.lock().unwrap().updater = Arc::new(Mutex::new(updater));
        this
    }
    fn get_value(&self) -> Result<T, String> {
        self.updater.lock().unwrap().refresh()?;
        Ok(self.value.lock().unwrap().clone())
    }
}
