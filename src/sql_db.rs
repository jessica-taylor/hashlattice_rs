use std::marker::PhantomData;
use sqlite::{Connection, State, Statement};

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
    fn initialize(&self) {
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_value (
            key BLOB PRIMARY KEY,
            value BLOB,
            pinned INTEGER
        )").unwrap();
        self.conn.execute("CREATE TABLE IF NOT EXISTS key_dep (
            key BLOB PRIMARY KEY,
            dep BLOB
        )").unwrap();
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
        let value = rmp_serde::to_vec(&value).unwrap();
        let mut stmt = self.conn.prepare("INSERT INTO key_value (key, value, pinned) VALUES (:key, :value, false)").unwrap()
            .bind_by_name(":key", &*key).unwrap()
            .bind_by_name(":value", &*value).unwrap();
        if stmt.next().unwrap() != State::Done {
            return Err("Failed to insert value".to_string());
        }
        for dep in deps {
            let dep = rmp_serde::to_vec(&dep).unwrap();
            stmt = self.conn.prepare("INSERT INTO key_dep (key, dep) VALUES (:key, :dep)").unwrap()
                .bind_by_name(":key", &*key).unwrap()
                .bind_by_name(":dep", &*dep).unwrap();
            if stmt.next().unwrap() != State::Done {
                continue;
            } else {
                return Err("Failed to insert dependency".to_string());
            }
        }
        Ok(())
    }

    fn is_pinned(&self, key: &M::Key) -> Result<bool, String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("SELECT * FROM key_value WHERE key = :key AND pinned = true").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        Ok(stmt.next().unwrap() == State::Row)
    }

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Result<(), String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("UPDATE key_value SET pinned = :pinned WHERE key = :key").unwrap()
            .bind_by_name(":key", &*key).unwrap()
            .bind_by_name(":pinned", pin as i64).unwrap();
        if stmt.next().unwrap() == State::Done {
            Ok(())
        } else {
            Err("Failed to update pin".to_string())
        }
    }

    fn clear_value_deps(&mut self, key: &M::Key) -> Result<(), String> {
        let key = rmp_serde::to_vec(key).unwrap();
        let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE key = :key").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        if stmt.next().unwrap() != State::Done {
            return Err("Failed to delete value".to_string());
        }
        stmt = self.conn.prepare("DELETE FROM key_dep WHERE key = :key").unwrap()
            .bind_by_name(":key", &*key).unwrap();
        if stmt.next().unwrap() == State::Done {
            Ok(())
        } else {
            Err("Failed to delete dependencies".to_string())
        }
    }

    fn clear_unpinned(&mut self) -> Result<(), String> {
        let mut stmt = self.conn.prepare("DELETE FROM key_value WHERE pinned = false").unwrap();
        if stmt.next().unwrap() != State::Done {
            return Err("Failed to delete values".to_string())
        }
        stmt = self.conn.prepare("DELETE FROM key_dep WHERE key NOT IN (SELECT key FROM key_value)").unwrap();
        if stmt.next().unwrap() == State::Done {
            Ok(())
        } else {
            Err("Failed to delete dependencies".to_string())
        }
    }
}
