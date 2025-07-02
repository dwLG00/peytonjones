

pub trait Recursible {
    fn recurse(&self, f: fn(Self) -> Self) -> Self;
}

pub fn metabolize<S, T, U>(st: (S, Result<T, U>)) -> Result<(S, T), U> {
    match st.1 {
        Ok(t) => Ok((st.0, t)),
        Err(u) => Err(u)
    }
}

pub fn join<T, E>(r1: Result<T, E>, r2: Result<T, E>) -> Result<(T, T), E> {
    match r1 {
        Ok(t1) => match r2 {
            Ok(t2) => Ok((t1, t2)),
            Err(e) => Err(e)
        },
        Err(e) => Err(e)
    }
}