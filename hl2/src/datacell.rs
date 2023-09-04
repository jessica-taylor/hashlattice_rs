
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
    updater: Mutex<CellUpdater>,
    value: Mutex<T>,
    update_fn: Box<dyn FnMut() -> Result<T, String>>,
}

impl<T : Clone> DataCell<T> {
    fn new<F : FnMut() -> Result<T, String> + 'static>(value: T, update_fn: F) -> Arc<Mutex<Self>> {
        let this = Arc::new(Mutex::new(Self {
            updater: Mutex::new(CellUpdater::new(|| Ok(()))),
            value: Mutex::new(value),
            update_fn: Box::new(update_fn)
        }));
        let this2 = this.clone();
        let updater = CellUpdater::new(|| {
            Ok(()) // TODO
        });
        this.lock().unwrap().updater = Mutex::new(updater);
        this
    }
}

// struct DataCellContents<T> {
//     value: T,
//     dirty: bool,
//     dependents: Vec<Weak<Mutex<DataCellContents<T>>>>,
//     dependencies: Vec<Arc<Mutex<DataCellContents<T>>>>,
// }
// pub struct DataCell<T> {
//     contents: Arc<Mutex<DataCellContents<T>>>
// }
