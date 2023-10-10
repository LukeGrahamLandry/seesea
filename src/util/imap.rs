//! There were several places I was using a HashMap<Ssa, _>,
//! which is dumb because SSAs are sequential so they could just be an index into an array.
//! This does that with the same API as a hash map, keeps key type safety, and accounts for inserting entries out of order.
//! The only downside is wasting memory if you have gaps between indexes.

use crate::ir::{Label, Ssa};
use std::borrow::Borrow;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

pub trait ToIndex {
    fn new(index: usize) -> Self;
    fn get_index(&self) -> usize;
}

#[derive(Debug, Clone)]
pub struct IndexMap<Key: ToIndex, Value> {
    values: Vec<Option<Value>>,
    count: usize,
    _p: PhantomData<Key>,
}

impl<Key: ToIndex, Value> IndexMap<Key, Value> {
    pub fn with_capacity(cap: usize) -> IndexMap<Key, Value> {
        IndexMap {
            values: (0..cap).map(|_| None).collect(), // I think the specialized FromIter for Vec knows to set the capacity TODO: make sure
            count: 0,
            _p: Default::default(),
        }
    }

    pub fn init(value: Value, cap: usize) -> IndexMap<Key, Value>
    where
        Value: Clone,
    {
        IndexMap {
            values: (0..cap).map(|_| Some(value.clone())).collect(),
            count: 0,
            _p: Default::default(),
        }
    }

    pub fn insert(&mut self, k: Key, v: Value) -> Option<Value> {
        let i = k.get_index();
        if self.values.len() <= i {
            self.values.extend((self.values.len()..=i).map(|_| None));
        }
        let prev = self.values[i].take();
        if prev.is_none() {
            self.count += 1;
        }
        self.values[i] = Some(v);
        prev
    }

    pub fn get(&self, k: &Key) -> Option<&Value> {
        if self.values.len() <= k.get_index() {
            None
        } else {
            match &self.values[k.get_index()] {
                None => None,
                Some(v) => Some(v),
            }
        }
    }

    pub fn get_mut(&mut self, k: &Key) -> Option<&mut Value> {
        if self.values.len() <= k.get_index() {
            None
        } else {
            match &mut self.values[k.get_index()] {
                None => None,
                Some(v) => Some(v),
            }
        }
    }

    pub fn len(&self) -> usize {
        self.count
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.values
            .iter()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
    }

    pub fn iter(&self) -> impl Iterator<Item = (Key, &Value)> {
        self.values
            .iter()
            .filter(|v| v.is_some())
            .map(|v| v.as_ref().unwrap())
            .enumerate()
            .map(|(i, v)| (Key::new(i), v))
    }
}

impl<Key: ToIndex, Value, BK: Borrow<Key>> Index<BK> for IndexMap<Key, Value> {
    type Output = Value;

    fn index(&self, index: BK) -> &Value {
        self.values[index.borrow().get_index()].as_ref().unwrap()
    }
}

impl<Key: ToIndex, Value, BK: Borrow<Key>> IndexMut<BK> for IndexMap<Key, Value> {
    fn index_mut(&mut self, index: BK) -> &mut Value {
        self.values[index.borrow().get_index()].as_mut().unwrap()
    }
}

impl ToIndex for Ssa {
    fn new(index: usize) -> Self {
        Ssa(index)
    }

    fn get_index(&self) -> usize {
        self.0
    }
}

impl ToIndex for Label {
    fn new(index: usize) -> Self {
        Label(index)
    }

    fn get_index(&self) -> usize {
        self.0
    }
}

impl ToIndex for usize {
    fn new(index: usize) -> Self {
        index
    }

    fn get_index(&self) -> usize {
        *self
    }
}

impl<Key: ToIndex, Value> Default for IndexMap<Key, Value> {
    fn default() -> Self {
        IndexMap {
            values: vec![],
            count: 0,
            _p: Default::default(),
        }
    }
}

impl ToIndex for u32 {
    fn new(index: usize) -> Self {
        index as u32
    }

    fn get_index(&self) -> usize {
        *self as usize
    }
}
