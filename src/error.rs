use anyhow::Error;


pub type Res<T> = Result<T, Error>;

pub fn to_string_result<T>(res: Res<T>) -> Result<T, String> {
    res.map_err(|e| format!("{}", e))
}
