#[derive(Debug, Clone, Default)]
/// Tarjan's Union-Find Data structure
pub struct DisjointSet {
    /// Parent information indexed directly by a dense caller-provided id.
    /// `usize::MAX` marks ids that have not been inserted.
    parent: Vec<usize>,
}

impl DisjointSet {
    pub fn new() -> Self {
        DisjointSet { parent: Vec::new() }
    }

    pub fn make_set(&mut self, id: usize) {
        if self.parent.len() <= id {
            self.parent.resize(id + 1, usize::MAX);
        }
        if self.parent[id] != usize::MAX {
            return;
        }
        self.parent[id] = id;
    }

    /// Returns Some(num), num is the tag of subset in which x is.
    /// If x is not in the data structure, it returns None.
    pub fn find(&mut self, id: usize) -> Option<usize> {
        if self.parent.get(id).copied().unwrap_or(usize::MAX) == usize::MAX {
            return None;
        }
        let ret = Self::find_internal(&mut self.parent, id);
        Some(ret)
    }

    fn find_internal(p: &mut Vec<usize>, n: usize) -> usize {
        if p[n] != n {
            let parent = p[n];
            p[n] = Self::find_internal(p, parent);
            p[n]
        } else {
            n
        }
    }

    /// Union the subsets to which x and y belong.
    /// If it returns `Some<u32>`, it is the tag for unified subset.
    /// If it returns `None`, at least one of x and y is not in the
    /// disjoint-set.
    pub fn union(&mut self, x: usize, y: usize) -> Option<usize> {
        let (x_root, y_root) = match (self.find(x), self.find(y)) {
            (Some(x), Some(y)) => (x, y),
            _ => {
                return None;
            }
        };

        self.parent[x_root] = y_root;
        Some(y_root)
    }
}

#[test]
fn it_works() {
    let mut ds = DisjointSet::new();
    ds.make_set(1);
    ds.make_set(2);
    ds.make_set(3);

    assert!(ds.find(1) != ds.find(2));
    assert!(ds.find(2) != ds.find(3));
    ds.union(1, 2).unwrap();
    ds.union(2, 3).unwrap();
    assert!(ds.find(1) == ds.find(3));

    assert!(ds.find(4).is_none());
    ds.make_set(4);
    assert!(ds.find(4).is_some());

    ds.make_set(5);
    assert!(ds.find(5) != ds.find(3));

    ds.union(5, 4).unwrap();
    ds.union(2, 4).unwrap();

    assert!(ds.find(5) == ds.find(3));
}
