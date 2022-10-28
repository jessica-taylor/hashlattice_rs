use std::error::Error;


pub type Res<T> = Result<T, Box<dyn Error>>;

pub fn str_error<T>(s: &str) -> Res<T> {
    Err(Box::<dyn Error>::from(s))
}
