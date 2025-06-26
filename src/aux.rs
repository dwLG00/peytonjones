

pub trait Recursible {
    fn recurse(&self, f: fn(Self) -> Self) -> Self;
}