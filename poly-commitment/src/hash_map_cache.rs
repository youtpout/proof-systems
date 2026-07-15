use std::{
    cmp::Eq,
    collections::HashMap,
    hash::Hash,
    ops::Deref,
    sync::{Arc, Mutex, OnceLock},
};

/// A concurrent memoization cache with per-key initialization.
///
/// The map itself is guarded by a mutex, but values are initialized through a
/// per-key `OnceLock` OUTSIDE that lock: generating a value for one key (e.g.
/// a multi-second Lagrange-basis computation) neither blocks lookups nor
/// serializes generations for other keys. Two threads racing on the same key
/// compute it once — the second blocks on the `OnceLock` until it is ready.
#[derive(Debug, Clone, Default)]
pub struct HashMapCache<Key: Hash, Value> {
    contents: Arc<Mutex<HashMap<Key, Arc<OnceLock<Value>>>>>,
}

impl<Key: Hash + Eq, Value> HashMapCache<Key, Value> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            contents: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    #[must_use]
    pub(crate) fn new_from_hashmap(hashmap: HashMap<Key, Arc<Value>>) -> Self {
        let contents = hashmap
            .into_iter()
            .map(|(key, value)| {
                let cell = OnceLock::new();
                let _ = cell.set(
                    Arc::try_unwrap(value).unwrap_or_else(|_| panic!("unique cache value")),
                );
                (key, Arc::new(cell))
            })
            .collect();
        Self {
            contents: Arc::new(Mutex::new(contents)),
        }
    }

    fn cell(&self, key: Key) -> Arc<OnceLock<Value>> {
        let mut hashmap = self.contents.lock().unwrap();
        Arc::clone(
            hashmap
                .entry(key)
                .or_insert_with(|| Arc::new(OnceLock::new())),
        )
    }

    /// Sets a value by key only if it hasn't already been set
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    pub fn set_once(&self, key: Key, value: Value) {
        let _ = self.cell(key).set(value);
    }

    /// Retrieves a cached value by key, or generates and caches it using the
    /// provided closure. The generator runs outside the map lock, so distinct
    /// keys generate concurrently and the same key generates exactly once.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    pub fn get_or_generate<F: FnOnce() -> Value>(
        &self,
        key: Key,
        generator: F,
    ) -> impl Deref<Target = Value> + '_ {
        let cell = self.cell(key);
        cell.get_or_init(generator);
        CacheRef(cell)
    }

    /// Returns `true` if the cache contains a fully initialized value for the
    /// given key.
    ///
    /// # Panics
    ///
    /// Panics if the internal mutex is poisoned.
    pub fn contains_key(&self, key: &Key) -> bool {
        self.contents
            .lock()
            .unwrap()
            .get(key)
            .is_some_and(|cell| cell.get().is_some())
    }
}

/// Owning handle to an initialized cache entry.
pub struct CacheRef<Value>(Arc<OnceLock<Value>>);

impl<Value> Deref for CacheRef<Value> {
    type Target = Value;

    fn deref(&self) -> &Value {
        self.0.get().expect("initialized by get_or_generate")
    }
}

#[allow(clippy::implicit_hasher)]
#[allow(clippy::fallible_impl_from)]
impl<Key: Hash + Eq + Clone, Value: Clone> From<HashMapCache<Key, Value>>
    for HashMap<Key, Arc<Value>>
{
    fn from(cache: HashMapCache<Key, Value>) -> Self {
        cache
            .contents
            .lock()
            .unwrap()
            .iter()
            .filter_map(|(key, cell)| {
                cell.get()
                    .map(|value| (key.clone(), Arc::new(value.clone())))
            })
            .collect()
    }
}
