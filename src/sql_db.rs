use std::collections::BTreeSet;
use std::marker::PhantomData;

use anyhow::bail;
use sqlite::{Connection, State};

use crate::error::Res;
use crate::tagged_mapping::TaggedMapping;
use crate::db::DepDB;


pub struct SqlDepDB<M: TaggedMapping> {
    conn: Connection,
    phantom: PhantomData<fn() -> M>,
}

impl<M: TaggedMapping> SqlDepDB<M> {
    pub fn new(path: &str) -> Res<SqlDepDB<M>> {
        let conn = Connection::open(path)?;
        Ok(SqlDepDB {
            conn,
            phantom: PhantomData,
        })
    }
    pub fn initialize(&mut self) -> Res<()>{
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_value (
            key BLOB PRIMARY KEY,
            value BLOB,
            pinned INTEGER,
            live INTEGER,
            dirty INTEGER
        )")?;
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_dep (
            key BLOB,
            dep BLOB
        )")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_dep_key ON key_dep (key)")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_dep_dep ON key_dep (dep)")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_value_live ON key_value (live) WHERE live = true")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_value_dirty ON key_value (dirty) WHERE live = true")?;
        Ok(())
    }

    fn set_live_raw(&mut self, key: &[u8]) -> Res<()> {
        let mut stmt = self.conn.prepare("UPDATE key_value SET live = (pinned OR EXISTS (SELECT 1 FROM key_dep WHERE dep = key_value.key)) WHERE key = :key")?
            .bind_by_name(":key", key)?;
        if stmt.next()? != State::Done {
            bail!("set_live_raw: unexpected result");
        }
        Ok(())
    }

    fn is_pinned_raw(&self, key: &[u8]) -> Res<bool> {
        let mut stmt = self.conn.prepare("SELECT 1 FROM key_value WHERE key = :key AND pinned = true")?
            .bind_by_name(":key", &*key)?;
        Ok(stmt.next()? == State::Row)
    }

    fn set_dependents_dirty_raw(&mut self, key: &[u8]) -> Res<()> {
        let mut non_dirty_deps = BTreeSet::new();
        {
            let mut stmt = self.conn.prepare("SELECT dep FROM key_dep WHERE key = :key AND dirty = true")?
                .bind_by_name(":key", &*key)?;
            while stmt.next()? != State::Done {
                let dep = stmt.read::<Vec<u8>>(0)?;
                non_dirty_deps.insert(dep);
            }
        };
        for dep in non_dirty_deps {
            {
                let mut stmt = self.conn.prepare("UPDATE key_value SET dirty = true WHERE key :key")?
                    .bind_by_name(":key", &*dep)?;
                if stmt.next()? != State::Done {
                    bail!("set_dependents_dirty: unexpected result");
                }
            }
            self.set_dependents_dirty_raw(&dep)?;
        }
        Ok(())
    }

    fn clear_value_deps_raw(&mut self, key: &[u8]) -> Res<()> {
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE key = :key")?
                .bind_by_name(":key", key)?;
            if stmt.next()? != State::Done {
                bail!("Failed to delete value");
            }
        }
        self.set_dependents_dirty_raw(key)?;
        let mut old_deps: Vec<Vec<u8>> = Vec::new();
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_dep WHERE key = :key RETURNING dep")?
                .bind_by_name(":key", key)?;
            while stmt.next()? != State::Done {
                old_deps.push(stmt.read::<Vec<u8>>(0)?);
            }
        }
        for dep in old_deps {
            self.set_live_raw(&dep)?;
        }
        Ok(())
    }
    fn is_dirty_raw(&self, key: &[u8]) -> Res<bool> {
        let mut stmt = self.conn.prepare("SELECT 1 FROM key_value WHERE key = :key AND dirty = true")?
            .bind_by_name(":key", key)?;
        Ok(stmt.next()? == State::Row)
    }

}

impl<M: TaggedMapping> DepDB<M> for SqlDepDB<M> {
    fn has_value(&self, key: &M::Key) -> Res<bool> {
        let key = rmp_serde::to_vec(key)?;
        let mut stmt = self.conn.prepare("SELECT 1 FROM key_value WHERE key = :key")?
            .bind_by_name(":key", &*key)?;
        Ok(stmt.next()? == State::Row)
    }

    fn get_value(&self, key: &M::Key) -> Res<Option<M::Value>> {
        let key = rmp_serde::to_vec(key)?;
        let mut stmt = self.conn.prepare("SELECT value FROM key_value WHERE key = :key")?
            .bind_by_name(":key", &*key)?;
        if stmt.next()? == State::Row {
            let value = stmt.read::<Vec<u8>>(0)?;
            let value = rmp_serde::from_slice(&value)?;
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps_vec: Vec<M::Key>) -> Res<()> {
        let key = rmp_serde::to_vec(&key)?;
        let value = rmp_serde::to_vec(&value)?;
        let mut deps = BTreeSet::<Vec<u8>>::new();
        for dep in deps_vec {
            deps.insert(rmp_serde::to_vec(&dep)?);
        }
        let same_value = {
            let mut stmt = self.conn.prepare("SELECT value FROM key_value WHERE key = :key")?
                .bind_by_name(":key", &*key)?;
            if stmt.next()? == State::Row {
                let old_value = stmt.read::<Vec<u8>>(0)?;
                old_value == value
            } else {
                false
            }
        };
        let old_deps = {
            let mut stmt = self.conn.prepare("SELECT dep FROM key_dep WHERE key = :key")?
                .bind_by_name(":key", &*key)?;
            let mut old_deps = BTreeSet::new();
            while stmt.next()? != State::Done {
                let dep = stmt.read::<Vec<u8>>(0)?;
                old_deps.insert(dep);
            }
            old_deps
        };
        if same_value && old_deps == deps {
            let mut stmt = self.conn.prepare("UPDATE key_value SET dirty = false WHERE key = :key")?
                .bind_by_name(":key", &*key)?;
            if stmt.next()? != State::Done {
                bail!("set_value_deps: unexpected result");
            }
            return Ok(());
        }
        if !same_value {
            self.set_dependents_dirty_raw(&key)?;
        }
        let already_pinned = self.is_pinned_raw(&key)?;
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE key = :key")?
                .bind_by_name(":key", &*key)?;
            if stmt.next()? != State::Done {
                bail!("Failed to delete value");
            }
        }
        {
            let mut stmt = self.conn.prepare("INSERT INTO key_value (key, value, pinned, live, dirty) VALUES (:key, :value, :pinned, false, false)")?
                .bind_by_name(":key", &*key)?
                .bind_by_name(":value", &*value)?
                .bind_by_name(":pinned", already_pinned as i64)?;
            if stmt.next()? != State::Done {
                bail!("Failed to insert value");
            }
        }
        for old_dep in &old_deps {
            if !deps.contains(old_dep) {
                {
                    let mut stmt = self.conn.prepare("DELETE FROM key_dep WHERE key = :key AND dep = :dep")?
                        .bind_by_name(":key", &*key)?
                        .bind_by_name(":dep", &**old_dep)?;
                    if stmt.next()? != State::Done {
                        bail!("Failed to delete dependency");
                    }
                }
                self.set_live_raw(&old_dep)?;
            }
        }
        for dep in deps {
            if !old_deps.contains(&dep) {
                {
                    let mut stmt = self.conn.prepare("INSERT INTO key_dep (key, dep) VALUES (:key, :dep)")?
                        .bind_by_name(":key", &*key)?
                        .bind_by_name(":dep", &*dep)?;
                    if stmt.next()? != State::Done {
                        bail!("Failed to insert dependency");
                    }
                }
                self.set_live_raw(&dep)?;
            }
        }
        self.set_live_raw(&key)?;
        Ok(())
    }

    fn is_pinned(&self, key: &M::Key) -> Res<bool> {
        let key = rmp_serde::to_vec(key)?;
        self.is_pinned_raw(&key)
    }

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Res<()> {
        let key = rmp_serde::to_vec(key)?;
        {
            let mut stmt = self.conn.prepare("UPDATE key_value SET pinned = :pinned WHERE key = :key")?
                .bind_by_name(":key", &*key)?
                .bind_by_name(":pinned", pin as i64)?;
            if stmt.next()? != State::Done {
                bail!("Failed to update pin");
            }
        }
        self.set_live_raw(&key)?;
        Ok(())
    }

    fn clear_value_deps(&mut self, key: &M::Key) -> Res<()> {
        let key = rmp_serde::to_vec(key)?;
        self.clear_value_deps_raw(&*key)
    }

    fn clear_dead(&mut self) -> Res<()> {
        loop {
            let mut to_delete = Vec::new();
            {
                let mut stmt = self.conn.prepare("SELECT key FROM key_value WHERE live = false")?;
                while stmt.next()? == State::Row {
                    to_delete.push(stmt.read::<Vec<u8>>(0)?);
                }
            }
            if to_delete.is_empty() {
                return Ok(());
            }
            for del_key in to_delete {
                self.clear_value_deps_raw(&del_key)?;
            }
        }
    }

    fn is_dirty(&self, key: &M::Key) -> Res<bool> {
        let key = rmp_serde::to_vec(key)?;
        self.is_dirty_raw(&key)
    }

    fn get_dirty(&mut self) -> Res<Vec<M::Key>> {
        let mut stmt = self.conn.prepare("SELECT key FROM key_value WHERE dirty = true")?;
        let mut dirty = Vec::new();
        while stmt.next()? == State::Row {
            let key = stmt.read::<Vec<u8>>(0)?;
            let key = rmp_serde::from_slice(&key)?;
            dirty.push(key);
        }
        Ok(dirty)
    }
}
