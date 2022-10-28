use std::collections::BTreeSet;
use std::marker::PhantomData;
use sqlite::{Connection, State};

use crate::error::{Res, str_error};
use crate::tagged_mapping::TaggedMapping;
use crate::db::DepDB;


struct SqlDepDB<M: TaggedMapping> {
    conn: Connection,
    phantom: PhantomData<fn() -> M>,
}

impl<M: TaggedMapping> SqlDepDB<M> {
    fn new(path: &str) -> Res<SqlDepDB<M>> {
        let conn = Connection::open(path)?;
        Ok(SqlDepDB {
            conn,
            phantom: PhantomData,
        })
    }
    fn initialize(&self) -> Res<()>{
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_value (
            key BLOB PRIMARY KEY,
            value BLOB,
            pinned INTEGER,
            live INTEGER
        )")?;
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_dep (
            key BLOB,
            dep BLOB
        )")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_dep_key ON key_dep (key)")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_dep_dep ON key_dep (dep)")?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_value_live ON key_value (live)")?;
        Ok(())
    }

    fn set_live_raw(&mut self, key: &[u8]) -> Res<()> {
        let mut stmt = self.conn.prepare("UPDATE key_value SET live = (pinned OR EXISTS (SELECT 1 FROM key_dep WHERE dep = key_value.key)) WHERE key = :key")?
            .bind_by_name(":key", key)?;
        if stmt.next()? != State::Done {
            return str_error("set_live_raw: unexpected result");
        }
        Ok(())
    }

    fn is_pinned_raw(&self, key: &[u8]) -> Res<bool> {
        let mut stmt = self.conn.prepare("SELECT 1 FROM key_value WHERE key = :key AND pinned = true")?
            .bind_by_name(":key", &*key)?;
        Ok(stmt.next()? == State::Row)
    }

    fn clear_value_deps_raw(&mut self, key: &[u8]) -> Res<()> {
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE key = :key")?
                .bind_by_name(":key", key)?;
            if stmt.next()? != State::Done {
                return str_error("Failed to delete value");
            }
        }
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

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Res<()> {
        let key = rmp_serde::to_vec(&key)?;
        let already_pinned = self.is_pinned_raw(&key)?;
        let mut old_deps = BTreeSet::new();
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_dep WHERE key = :key RETURNING dep")?
                .bind_by_name(":key", &*key)?;
            while let State::Row = stmt.next()? {
                let dep = stmt.read::<Vec<u8>>(0)?;
                old_deps.insert(dep);
            }
        }
        let value = rmp_serde::to_vec(&value)?;
        {
            let mut stmt = self.conn.prepare("INSERT INTO key_value (key, value, pinned, live) VALUES (:key, :value, :pinned, false)")?
                .bind_by_name(":key", &*key)?
                .bind_by_name(":value", &*value)?
                .bind_by_name(":pinned", already_pinned as i64)?;
            if stmt.next()? != State::Done {
                return str_error("Failed to insert value");
            }
        }
        let mut deps_set = BTreeSet::new();
        for dep in deps {
            let dep = rmp_serde::to_vec(&dep)?;
            {
                let mut stmt = self.conn.prepare("INSERT INTO key_dep (key, dep) VALUES (:key, :dep)")?
                    .bind_by_name(":key", &*key)?
                    .bind_by_name(":dep", &*dep)?;
                if stmt.next()? != State::Done {
                    return str_error("Failed to insert dependency");
                }
            }
            if !old_deps.contains(&dep) {
                self.set_live_raw(&dep)?;
            }
            deps_set.insert(dep);
        }
        for dep in old_deps {
            if !deps_set.contains(&dep) {
                self.set_live_raw(&dep)?;
            }
        }
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
                return str_error("Failed to update pin");
            }
        }
        self.set_live_raw(&key)?;
        Ok(())
    }

    fn clear_value_deps(&mut self, key: &M::Key) -> Res<()> {
        let key = rmp_serde::to_vec(key)?;
        self.clear_value_deps_raw(&*key)
    }

    fn clear_unpinned(&mut self) -> Res<()> {
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
}
