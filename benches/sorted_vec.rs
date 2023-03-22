#[derive(Default, Clone)]
pub struct SortedVec<K, V> {
    store: Vec<(K, V)>,
}

impl<K: Ord + Eq + Copy + Clone, V> SortedVec<K, V> {
    pub fn new() -> Self {
        Self {
            store: Default::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.store.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.store.iter().map(|kv| (&kv.0, &kv.1))
    }

    pub fn insert(&mut self, k: K, v: V) {
        match self.store.binary_search_by_key(&k, |i| i.0) {
            Ok(idx) => {
                self.store[idx].1 = v;
            }
            Err(idx) => {
                self.store.insert(idx, (k, v));
            }
        }
    }

    pub fn remove(&mut self, k: &K) -> Option<(K, V)> {
        match self.store.binary_search_by_key(k, |i| i.0) {
            Ok(idx) => Some(self.store.remove(idx)),
            Err(_) => None,
        }
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        match self.store.binary_search_by_key(&k, |i| &i.0) {
            Ok(idx) => Some(&self.store[idx].1),
            Err(_) => None,
        }
    }
}
