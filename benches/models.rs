use std::{cmp::Ordering, rc::Rc};

#[derive(Clone, Copy, Debug)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}
impl Eq for Point {}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.x.partial_cmp(&other.x) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.y.partial_cmp(&other.y)
    }
}

impl Ord for Point {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Point3<const N: usize> {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    fill: [u8; N],
}

impl<const N: usize> PartialEq for Point3<N> {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y && self.z == other.z
    }
}
impl<const N: usize> Eq for Point3<N> {}

impl<const N: usize> PartialOrd for Point3<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.x.partial_cmp(&other.x) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.y.partial_cmp(&other.y) {
            Some(Ordering::Equal) => {}
            ord => return ord,
        }
        self.z.partial_cmp(&other.z)
    }
}

impl<const N: usize> Ord for Point3<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

#[derive(Default, Copy, Clone, Debug)]
pub struct Value {
    _data_0: [u8; 24],
    _data_1: [u8; 24],
}

pub trait TestKey: sweep_bptree::Key {
    fn from_i(i: usize) -> Self;

    fn name() -> String;
}

impl TestKey for Point {
    fn from_i(i: usize) -> Self {
        Point {
            x: i as f64,
            y: i as f64,
        }
    }

    fn name() -> String {
        "Point".into()
    }
}

impl<const N: usize> TestKey for Point3<N> {
    fn from_i(i: usize) -> Self {
        Point3 {
            x: i as f64,
            y: i as f64,
            z: i as f64,
            fill: [0; N],
        }
    }

    fn name() -> String {
        format!("Point3<{N}>")
    }
}

impl TestKey for String {
    fn from_i(i: usize) -> Self {
        format!("key_{:030}", i)
    }

    fn name() -> String {
        "String".into()
    }
}

impl TestKey for Rc<String> {
    fn from_i(i: usize) -> Self {
        Rc::new(format!("key_{:030}", i))
    }

    fn name() -> String {
        "Rc<String>".into()
    }
}
