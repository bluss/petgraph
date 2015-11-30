//! `GraphMap<N, E>` is an undirected graph where node values are mapping keys.

use std::hash::{Hash};
use std::collections::HashMap;
use std::iter::Cloned;
use std::collections::hash_map::{
    Keys,
};
use std::collections::hash_map::Iter as HashmapIter;
use std::slice::{
    Iter,
};
use std::fmt;
use std::iter::FromIterator;
use std::ops::{Index, IndexMut};

use IntoWeightedEdge;

/// `GraphMap<N, E>` is an undirected graph, with generic node values `N` and edge weights `E`.
///
/// It uses an combined adjacency list and sparse adjacency matrix representation, using **O(|V|
/// + |E|)** space, and allows testing for edge existance in constant time.
///
/// The node type `N` must implement `Copy` and will be used as node identifier, duplicated
/// into several places in the data structure.
/// It must be suitable as a hash table key (implementing `Eq + Hash`).
/// The node type must also implement `Ord` so that the implementation can
/// order the pair (`a`, `b`) for an edge connecting any two nodes `a` and `b`.
///
/// `GraphMap` does not allow parallel edges, but self loops are allowed.
#[derive(Clone)]
pub struct GraphMap<N, E> {
    nodes: HashMap<N, Vec<N>>,
    edges: HashMap<(N, N), E>,
}

impl<N: Eq + Hash + fmt::Debug, E: fmt::Debug> fmt::Debug for GraphMap<N, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.nodes.fmt(f)
    }
}

/// Use their natual order to map the node pair (a, b) to a canonical edge id.
#[inline]
fn edge_key<N: Copy + Ord>(a: N, b: N) -> (N, N) {
    if a <= b { (a, b) } else { (b, a) }
}

/// A trait group for `GraphMap`'s node identifier.
pub trait NodeTrait : Copy + Ord + Hash {}
impl<N> NodeTrait for N where N: Copy + Ord + Hash {}

impl<N, E> GraphMap<N, E>
    where N: NodeTrait
{
    /// Create a new `GraphMap`.
    pub fn new() -> Self {
        GraphMap {
            nodes: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    /// Create a new `GraphMap` with estimated capacity.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        GraphMap {
            nodes: HashMap::with_capacity(nodes),
            edges: HashMap::with_capacity(edges),
        }
    }

    /// Return the current node and edge capacity of the graph.
    pub fn capacity(&self) -> (usize, usize) {
        (self.nodes.capacity(), self.edges.capacity())
    }

    /// Create a new `GraphMap` from an iterable of edges.
    ///
    /// Node values are taken directly from the list.
    /// Edge weights `E` may either be specified in the list,
    /// or they are filled with default values.
    ///
    /// Nodes are inserted automatically to match the edges.
    ///
    /// ```
    /// use petgraph::GraphMap;
    ///
    /// let gr = GraphMap::<_, ()>::from_edges(&[
    ///     (0, 1), (0, 2), (0, 3),
    ///     (1, 2), (1, 3),
    ///     (2, 3),
    /// ]);
    /// ```
    pub fn from_edges<I>(iterable: I) -> Self
        where I: IntoIterator,
              I::Item: IntoWeightedEdge<N, E>
    {
        Self::from_iter(iterable)
    }

    /// Return the number of nodes in the graph.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Return the number of edges in the graph.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Remove all nodes and edges
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.edges.clear();
    }

    /// Add node `n` to the graph.
    pub fn add_node(&mut self, n: N) -> N {
        self.nodes.entry(n).or_insert_with(|| Vec::new());
        n
    }

    /// Return `true` if node `n` was removed.
    pub fn remove_node(&mut self, n: N) -> bool {
        let successors = match self.nodes.remove(&n) {
            None => return false,
            Some(sus) => sus,
        };
        for succ in successors.into_iter() {
            // remove all successor links
            self.remove_single_edge(&succ, &n);
            // Remove all edge values
            self.edges.remove(&edge_key(n, succ));
        }
        true
    }

    /// Return `true` if the node is contained in the graph.
    pub fn contains_node(&self, n: N) -> bool {
        self.nodes.contains_key(&n)
    }

    /// Add an edge connecting `a` and `b` to the graph.
    ///
    /// Inserts nodes `a` and/or `b` if they aren't already part of the graph.
    ///
    /// Return `true` if the edge did not previously exist.
    ///
    /// ```
    /// use petgraph::GraphMap;
    ///
    /// let mut g = GraphMap::new();
    /// g.add_edge(1, 2, -1);
    /// assert_eq!(g.node_count(), 2);
    /// assert_eq!(g.edge_count(), 1);
    /// ```
    pub fn add_edge(&mut self, a: N, b: N, edge_data: E) -> bool {
        if self.edges.insert(edge_key(a, b), edge_data).is_none() {
            // insert in the adjacency list if it's a new edge
            self.nodes.entry(a)
                      .or_insert_with(|| Vec::with_capacity(1))
                      .push(b);
            if a != b {
                self.nodes.entry(b)
                          .or_insert_with(|| Vec::with_capacity(1))
                          .push(a);
            }
            true
        } else {
            false
        }
    }

    /// Remove successor relation from a to b
    ///
    /// Return `true` if it did exist.
    fn remove_single_edge(&mut self, a: &N, b: &N) -> bool {
        match self.nodes.get_mut(a) {
            None => false,
            Some(sus) => {
                match sus.iter().position(|elt| elt == b) {
                    Some(index) => { sus.swap_remove(index); true }
                    None => false,
                }
            }
        }
    }

    /// Remove edge from `a` to `b` from the graph and return the edge weight.
    ///
    /// Return `None` if the edge didn't exist.
    ///
    /// ```
    /// use petgraph::GraphMap;
    ///
    /// let mut g = GraphMap::new();
    /// g.add_edge(1, 2, -1);
    ///
    /// let edge_data = g.remove_edge(2, 1);
    /// assert_eq!(edge_data, Some(-1));
    /// assert_eq!(g.edge_count(), 0);
    /// ```
    pub fn remove_edge(&mut self, a: N, b: N) -> Option<E> {
        let exist1 = self.remove_single_edge(&a, &b);
        let exist2 = if a != b { self.remove_single_edge(&b, &a) } else { exist1 };
        let weight = self.edges.remove(&edge_key(a, b));
        debug_assert!(exist1 == exist2 && exist1 == weight.is_some());
        weight
    }

    /// Return `true` if the edge connecting `a` with `b` is contained in the graph.
    pub fn contains_edge(&self, a: N, b: N) -> bool {
        self.edges.contains_key(&edge_key(a, b))
    }

    /// Return an iterator over the nodes of the graph.
    ///
    /// Iterator element type is `N`.
    pub fn nodes(&self) -> Nodes<N> {
        Nodes{iter: self.nodes.keys().cloned()}
    }

    /// Return an iterator over the nodes that are connected with `from` by edges.
    ///
    /// If the node `from` does not exist in the graph, return an empty iterator.
    ///
    /// Iterator element type is `N`.
    pub fn neighbors(&self, from: N) -> Neighbors<N> {
        Neighbors{iter:
            match self.nodes.get(&from) {
                Some(neigh) => neigh.iter(),
                None => [].iter(),
            }.cloned()
        }
    }

    /// Return an iterator over the nodes that are connected with `from` by edges,
    /// paired with the edge weight.
    ///
    /// If the node `from` does not exist in the graph, return an empty iterator.
    ///
    /// Iterator element type is `(N, &E)`.
    pub fn edges(&self, from: N) -> Edges<N, E> {
        Edges {
            from: from,
            iter: self.neighbors(from),
            edges: &self.edges,
        }
    }

    /// Return a reference to the edge weight connecting `a` with `b`, or
    /// `None` if the edge does not exist in the graph.
    pub fn edge_weight(&self, a: N, b: N) -> Option<&E> {
        self.edges.get(&edge_key(a, b))
    }

    /// Return a mutable reference to the edge weight connecting `a` with `b`, or
    /// `None` if the edge does not exist in the graph.
    pub fn edge_weight_mut(&mut self, a: N, b: N) -> Option<&mut E> {
        self.edges.get_mut(&edge_key(a, b))
    }

    /// Return an iterator over all edges of the graph with their weight in arbitrary order.
    ///
    /// Iterator element type is `((N, N), &E)`
    pub fn all_edges(&self) -> AllEdges<N, E> {
        AllEdges {
            inner: self.edges.iter()
        }
    }
}

/// Create a new `GraphMap` from an iterable of edges.
impl<N, E, Item> FromIterator<Item> for GraphMap<N, E>
    where Item: IntoWeightedEdge<N, E>,
          N: NodeTrait,
{
    fn from_iter<I>(iterable: I) -> Self
        where I: IntoIterator<Item=Item>,
    {
        let iter = iterable.into_iter();
        let (low, _) = iter.size_hint();
        let mut g = Self::with_capacity(0, low);
        g.extend(iter);
        g
    }
}

/// Extend the graph from an iterable of edges.
///
/// Nodes are inserted automatically to match the edges.
impl<N, E, Item> Extend<Item> for GraphMap<N, E>
    where Item: IntoWeightedEdge<N, E>,
          N: NodeTrait,
{
    fn extend<I>(&mut self, iterable: I)
        where I: IntoIterator<Item=Item>,
    {
        let iter = iterable.into_iter();
        let (low, _) = iter.size_hint();
        self.edges.reserve(low);

        for elt in iter {
            let (source, target, weight) = elt.into_weighted_edge();
            self.add_edge(source, target, weight);
        }
    }
}

/// Utitily macro -- reinterpret passed in macro arguments as items
macro_rules! items {
    ($($item:item)*) => ($($item)*);
}

macro_rules! iterator_wrap {
    ($name: ident <$($typarm:tt),*> where { $($bounds: tt)* }
     item: $item: ty,
     iter: $iter: ty,
     ) => (
        items! {
            pub struct $name <$($typarm),*> where $($bounds)* {
                iter: $iter,
            }
            impl<$($typarm),*> Iterator for $name <$($typarm),*>
                where $($bounds)*
            {
                type Item = $item;
                #[inline]
                fn next(&mut self) -> Option<Self::Item> {
                    self.iter.next()
                }

                #[inline]
                fn size_hint(&self) -> (usize, Option<usize>) {
                    self.iter.size_hint()
                }
            }
            impl<$($typarm),*> DoubleEndedIterator for $name <$($typarm),*>
                where $($bounds)*, $iter: DoubleEndedIterator<Item=$item>,
            {
                #[inline]
                fn next_back(&mut self) -> Option<Self::Item> {
                    self.iter.next_back()
                }
            }

            impl<$($typarm),*> ExactSizeIterator for $name <$($typarm),*>
                where $($bounds)*, $iter: ExactSizeIterator<Item=$item>,
            {
            }
        }
    );
}

iterator_wrap! {
    Nodes <'a, N> where { N: 'a + Clone }
    item: N,
    iter: Cloned<Keys<'a, N, Vec<N>>>,
}

iterator_wrap! {
    Neighbors <'a, N> where { N: 'a + Clone }
    item: N,
    iter: Cloned<Iter<'a, N>>,
}

pub struct Edges<'a, N, E: 'a> where N: 'a + NodeTrait {
    /// **Deprecated: should be private**
    pub from: N,
    /// **Deprecated: should be private**
    pub edges: &'a HashMap<(N, N), E>,
    /// **Deprecated: should be private**
    pub iter: Neighbors<'a, N>,
}

impl<'a, N, E> Iterator for Edges<'a, N, E>
    where N: 'a + NodeTrait, E: 'a
{
    type Item = (N, &'a E);
    fn next(&mut self) -> Option<(N, &'a E)>
    {
        match self.iter.next() {
            None => None,
            Some(b) => {
                let a = self.from;
                match self.edges.get(&edge_key(a, b)) {
                    None => unreachable!(),
                    Some(edge) => {
                        Some((b, edge))
                    }
                }
            }
        }
    }
}

pub struct AllEdges<'a, N, E: 'a> where N: 'a + NodeTrait {
    inner: HashmapIter<'a, (N, N), E>
}

impl<'a, N, E> Iterator for AllEdges<'a, N, E>
    where N: 'a + NodeTrait, E: 'a
{
    type Item = ((N, N), &'a E);
    fn next(&mut self) -> Option<((N, N), &'a E)>
    {
        match self.inner.next() {
            None => None,
            Some((k, v)) => Some((*k, v))
        }
    }
}

/// Index `GraphMap` by node pairs to access edge weights.
impl<N, E> Index<(N, N)> for GraphMap<N, E>
    where N: NodeTrait
{
    type Output = E;
    fn index(&self, index: (N, N)) -> &E
    {
        self.edge_weight(index.0, index.1).expect("GraphMap::index: no such edge")
    }
}

/// Index `GraphMap` by node pairs to access edge weights.
impl<N, E> IndexMut<(N, N)> for GraphMap<N, E>
    where N: NodeTrait
{
    fn index_mut(&mut self, index: (N, N)) -> &mut E
    {
        self.edge_weight_mut(index.0, index.1).expect("GraphMap::index: no such edge")
    }
}
