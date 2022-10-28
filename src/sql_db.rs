use std::marker::PhantomData;
use sqlite::{Connection, State};

use crate::tagged_mapping::TaggedMapping;
use crate::db::DepDB;


struct SqlDepDB<M: TaggedMapping> {
    conn: Connection,
    phantom: PhantomData<fn() -> M>,
}

impl<M: TaggedMapping> SqlDepDB<M> {
    fn new(path: &str) -> SqlDepDB<M> {
        let conn = Connection::open(path).unwrap();
        SqlDepDB {
            conn,
            phantom: PhantomData,
        }
    }
    fn initialize(&self) -> Result<(), String>{
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_value (
            key BLOB PRIMARY KEY,
            value BLOB,
            pinned INTEGER,
            live INTEGER
        )").map_err(|e| e.to_string())?;
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_dep (
            key BLOB PRIMARY KEY,
            dep BLOB
        )").map_err(|e| e.to_string())?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_dep_dep ON key_dep (dep)").map_err(|e| e.to_string())?;
        self.conn.execute("CREATE INDEX IF NOT EXISTS key_value_live ON key_value (live)").map_err(|e| e.to_string())?;
        Ok(())
    }

    fn set_live_raw(&mut self, key: &[u8]) -> Result<(), String> {
        let mut stmt = self.conn.prepare("UPDATE key_value SET live = (pinned OR EXISTS (SELECT 1 FROM key_dep WHERE dep = key_value.key)) WHERE key = :key").unwrap()
            .bind_by_name(":key", key).unwrap();
        if stmt.next().unwrap() != State::Done {
            return Err("set_live_raw: unexpected result".to_string());
        }
        Ok(())
    }

    fn clear_value_deps_raw(&mut self, key: &[u8]) -> Result<(), String> {
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE key = :key").unwrap()
                .bind_by_name(":key", key).unwrap();
            if stmt.next().unwrap() != State::Done {
                return Err("Failed to delete value".to_string());
            }
        }
        let mut old_deps: Vec<Vec<u8>> = Vec::new();
        {
            let mut stmt = self.conn.prepare("DELETE FROM key_dep WHERE key = :key RETURNING dep").unwrap()
                .bind_by_name(":key", key).unwrap();
            while stmt.next().unwrap() != State::Done {
                old_deps.push(stmt.read::<Vec<u8>>(0).unwrap());
            }
        }
        for dep in old_deps {
            self.set_live_raw(&dep)?;
        }
        Ok(())
    }
}

impl<M: TaggedMapping> DepDB<M> for SqlDepDB<M> {
    fn has_value(&self, key: &M::Key) -> Result<bool, String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("SELECT value FROM key_value WHERE key = :key").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        Ok(stmt.next().unwrap() == State::Row)
    }

    fn get_value(&self, key: &M::Key) -> Result<Option<M::Value>, String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("SELECT value FROM key_value WHERE key = :key").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        if stmt.next().unwrap() == State::Row {
            let value = stmt.read::<Vec<u8>>(0).unwrap();
            let value = rmp_serde::from_read_ref(&value).unwrap();
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Result<(), String> {
        let key = rmp_serde::to_vec(&key).unwrap();
        let mut old_deps = Vec::new();
        {
            let mut stmt = self.conn.prepare("SELECT dep FROM key_dep WHERE key = :key").unwrap()
                .bind_by_name(":key", &*key).unwrap();
            while let State::Row = stmt.next().unwrap() {
                let dep = stmt.read::<Vec<u8>>(0).unwrap();
                old_deps.push(dep);
            }
        }
        let value = rmp_serde::to_vec(&value).unwrap();
        {
            let mut stmt = self.conn.prepare("INSERT INTO key_value (key, value, pinned, live) VALUES (:key, :value, false, false)").unwrap()
                .bind_by_name(":key", &*key).unwrap()
                .bind_by_name(":value", &*value).unwrap();
            if stmt.next().unwrap() != State::Done {
                return Err("Failed to insert value".to_string());
            }
        }
        for dep in deps {
            let dep = rmp_serde::to_vec(&dep).unwrap();
            let mut stmt = self.conn.prepare("INSERT INTO key_dep (key, dep) VALUES (:key, :dep)").unwrap()
                .bind_by_name(":key", &*key).unwrap()
                .bind_by_name(":dep", &*dep).unwrap();
            if stmt.next().unwrap() != State::Done {
                return Err("Failed to insert dependency".to_string());
            }
            stmt = self.conn.prepare("UPDATE key_value SET live = true WHERE key = :dep").unwrap()
                .bind_by_name(":dep", &*dep).unwrap();
            if stmt.next().unwrap() != State::Done {
                return Err("Failed to update dependency".to_string());
            }
        }
        for dep in old_deps {
            self.set_live_raw(&dep)?;
        }
        Ok(())
    }

    fn is_pinned(&self, key: &M::Key) -> Result<bool, String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("SELECT 1 FROM key_value WHERE key = :key AND pinned = true").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        Ok(stmt.next().unwrap() == State::Row)
    }

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Result<(), String> {
        let key = rmp_serde::to_vec(key).unwrap();
        {
            let mut stmt = self.conn.prepare("UPDATE key_value SET pinned = :pinned WHERE key = :key").unwrap()
                .bind_by_name(":key", &*key).unwrap()
                .bind_by_name(":pinned", pin as i64).unwrap();
            if stmt.next().unwrap() != State::Done {
                return Err("Failed to update pin".to_string());
            }
        }
        self.set_live_raw(&key)?;
        Ok(())
    }

    fn clear_value_deps(&mut self, key: &M::Key) -> Result<(), String> {
        let key = rmp_serde::to_vec(key).unwrap();
        self.clear_value_deps_raw(&*key)
    }

    fn clear_unpinned(&mut self) -> Result<(), String> {
        loop {
            let mut to_delete = Vec::new();
            {
                let mut stmt = self.conn.prepare("SELECT key FROM key_value WHERE live = false").unwrap();
                while stmt.next().unwrap() == State::Row {
                    to_delete.push(stmt.read::<Vec<u8>>(0).unwrap());
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
