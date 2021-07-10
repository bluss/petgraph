//! Compute dominators of a control-flow graph.
//!
//! # The Dominance Relation
//!
//! In a directed graph with a root node **R**, a node **A** is said to *dominate* a
//! node **B** iff every path from **R** to **B** contains **A**.
//!
//! The node **A** is said to *strictly dominate* the node **B** iff **A** dominates
//! **B** and **A ≠ B**.
//!
//! The node **A** is said to be the *immediate dominator* of a node **B** iff it
//! strictly dominates **B** and there does not exist any node **C** where **A**
//! dominates **C** and **C** dominates **B**.

use std::cmp::Ordering;
use std::collections::{hash_map::Iter, HashMap, HashSet};
use std::hash::Hash;
use std::iter::FromIterator;

use crate::visit::{DfsPostOrder, GraphBase, IntoNeighbors, Visitable, Walker};

/// The dominance relation for some graph and root.
#[derive(Debug, Clone)]
pub struct Dominators<N>
where
    N: Copy + Eq + Hash,
{
    root: N,
    dominators: HashMap<N, N>,
}

impl<N> Dominators<N>
where
    N: Copy + Eq + Hash,
{
    /// Get the root node used to construct these dominance relations.
    pub fn root(&self) -> N {
        self.root
    }

    /// Get the immediate dominator of the given node.
    ///
    /// Returns `None` for any node that is not reachable from the root, and for
    /// the root itself.
    pub fn immediate_dominator(&self, node: N) -> Option<N> {
        if node == self.root {
            None
        } else {
            self.dominators.get(&node).cloned()
        }
    }

    /// Iterate over the given node's strict dominators.
    ///
    /// If the given node is not reachable from the root, then `None` is
    /// returned.
    pub fn strict_dominators(&self, node: N) -> Option<DominatorsIter<N>> {
        if self.dominators.contains_key(&node) {
            Some(DominatorsIter {
                dominators: self,
                node: self.immediate_dominator(node),
            })
        } else {
            None
        }
    }

    /// Iterate over all of the given node's dominators (including the given
    /// node itself).
    ///
    /// If the given node is not reachable from the root, then `None` is
    /// returned.
    pub fn dominators(&self, node: N) -> Option<DominatorsIter<N>> {
        if self.dominators.contains_key(&node) {
            Some(DominatorsIter {
                dominators: self,
                node: Some(node),
            })
        } else {
            None
        }
    }

    /// Iterate over all nodes immediately dominated by the given node (not
    /// including the given node itself).
    pub fn immediately_dominated_by(&self, node: N) -> DominatedByIter<N> {
        DominatedByIter {
            iter: self.dominators.iter(),
            node,
        }
    }
}

/// Iterator for a node's dominators.
#[derive(Debug, Clone)]
pub struct DominatorsIter<'a, N>
where
    N: 'a + Copy + Eq + Hash,
{
    dominators: &'a Dominators<N>,
    node: Option<N>,
}

impl<'a, N> Iterator for DominatorsIter<'a, N>
where
    N: 'a + Copy + Eq + Hash,
{
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.node.take();
        if let Some(next) = next {
            self.node = self.dominators.immediate_dominator(next);
        }
        next
    }
}

/// Iterator for nodes dominated by a given node.
#[derive(Debug, Clone)]
pub struct DominatedByIter<'a, N>
where
    N: 'a + Copy + Eq + Hash,
{
    iter: Iter<'a, N, N>,
    node: N,
}

impl<'a, N> Iterator for DominatedByIter<'a, N>
where
    N: 'a + Copy + Eq + Hash,
{
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter.next() {
            if next.1 == &self.node {
                return Some(*next.0);
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

/// The undefined dominator sentinel, for when we have not yet discovered a
/// node's dominator.
const UNDEFINED: usize = ::std::usize::MAX;

/// This is an implementation of the engineered ["Simple, Fast Dominance
/// Algorithm"][0] discovered by Cooper et al.
///
/// This algorithm is **O(|V|²)**, and therefore has slower theoretical running time
/// than the Lengauer-Tarjan algorithm (which is **O(|E| log |V|)**. However,
/// Cooper et al found it to be faster in practice on control flow graphs of up
/// to ~30,000 vertices. Take this with a grain of salt, and see the documentation for
/// `lengauer_tarjan` for details.
///
/// [0]: http://www.cs.rice.edu/~keith/EMBED/dom.pdf
pub fn simple_fast<G>(graph: G, root: G::NodeId) -> Dominators<G::NodeId>
where
    G: IntoNeighbors + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let (post_order, predecessor_sets) = simple_fast_post_order(graph, root);
    let length = post_order.len();
    debug_assert!(length > 0);
    debug_assert!(post_order.last() == Some(&root));

    // From here on out we use indices into `post_order` instead of actual
    // `NodeId`s wherever possible. This greatly improves the performance of
    // this implementation, but we have to pay a little bit of upfront cost to
    // convert our data structures to play along first.

    // Maps a node to its index into `post_order`.
    let node_to_post_order_idx: HashMap<_, _> = post_order
        .iter()
        .enumerate()
        .map(|(idx, &node)| (node, idx))
        .collect();

    // Maps a node's `post_order` index to its set of predecessors's indices
    // into `post_order` (as a vec).
    let idx_to_predecessor_vec =
        predecessor_sets_to_idx_vecs(&post_order, &node_to_post_order_idx, predecessor_sets);

    let mut dominators = vec![UNDEFINED; length];
    dominators[length - 1] = length - 1;

    let mut changed = true;
    while changed {
        changed = false;

        // Iterate in reverse post order, skipping the root.

        for idx in (0..length - 1).rev() {
            debug_assert!(post_order[idx] != root);

            // Take the intersection of every predecessor's dominator set; that
            // is the current best guess at the immediate dominator for this
            // node.

            let new_idom_idx = {
                let mut predecessors = idx_to_predecessor_vec[idx]
                    .iter()
                    .filter(|&&p| dominators[p] != UNDEFINED);
                let new_idom_idx = predecessors.next().expect(
                    "Because the root is initialized to dominate itself, and is the \
                     first node in every path, there must exist a predecessor to this \
                     node that also has a dominator",
                );
                predecessors.fold(*new_idom_idx, |new_idom_idx, &predecessor_idx| {
                    intersect(&dominators, new_idom_idx, predecessor_idx)
                })
            };

            debug_assert!(new_idom_idx < length);

            if new_idom_idx != dominators[idx] {
                dominators[idx] = new_idom_idx;
                changed = true;
            }
        }
    }

    // All done! Translate the indices back into proper `G::NodeId`s.

    debug_assert!(!dominators.iter().any(|&dom| dom == UNDEFINED));

    Dominators {
        root,
        dominators: dominators
            .into_iter()
            .enumerate()
            .map(|(idx, dom_idx)| (post_order[idx], post_order[dom_idx]))
            .collect(),
    }
}

fn intersect(dominators: &[usize], mut finger1: usize, mut finger2: usize) -> usize {
    loop {
        match finger1.cmp(&finger2) {
            Ordering::Less => finger1 = dominators[finger1],
            Ordering::Greater => finger2 = dominators[finger2],
            Ordering::Equal => return finger1,
        }
    }
}

fn predecessor_sets_to_idx_vecs<N>(
    post_order: &[N],
    node_to_post_order_idx: &HashMap<N, usize>,
    mut predecessor_sets: HashMap<N, HashSet<N>>,
) -> Vec<Vec<usize>>
where
    N: Copy + Eq + Hash,
{
    post_order
        .iter()
        .map(|node| {
            predecessor_sets
                .remove(node)
                .map(|predecessors| {
                    predecessors
                        .into_iter()
                        .map(|p| *node_to_post_order_idx.get(&p).unwrap())
                        .collect()
                })
                .unwrap_or_else(Vec::new)
        })
        .collect()
}

type PredecessorSets<NodeId> = HashMap<NodeId, HashSet<NodeId>>;

fn simple_fast_post_order<G>(
    graph: G,
    root: G::NodeId,
) -> (Vec<G::NodeId>, PredecessorSets<G::NodeId>)
where
    G: IntoNeighbors + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let mut post_order = vec![];
    let mut predecessor_sets = HashMap::new();

    for node in DfsPostOrder::new(graph, root).iter(graph) {
        post_order.push(node);

        for successor in graph.neighbors(node) {
            predecessor_sets
                .entry(successor)
                .or_insert_with(HashSet::new)
                .insert(node);
        }
    }

    (post_order, predecessor_sets)
}

/// An implementation of the dominators construction algorithm described in ["A
/// Fast Algorithm for Finding Dominators in a Flowgraph" by Thomas Lengauer and
/// Robert E. Tarjan][0].
///
/// This algorithm runs in **O(|E| log |V|)** time. This is a better theoretical
/// running time than the "Simple, Fast" algorithm by Cooper (see
/// `simple_fast`), but has higher start-up costs and memory requirements. The
/// "Simple, Fast" paper reported the tipping point where the Lengauer-Tarjan
/// algorithm outperformed theirs at CFGs with >= 30,000 vertices. Take this
/// with a grain of salt, however, as noted in ["Finding Dominators in Practice"
/// by Loukas Georgiadis, Robert E. Tarjan, and Renato F. Werneck][1]:
///
/// > Even on small instances, however, we did not observe the clear superiority
/// > of the ["Simple, Fast" algorithm] reported by Cooper et al.,
/// > which we attribute to their inefficient implementation of [the simple
/// > Lengauer-Tarjan algorithm].
///
/// Note that this function is an implementation of the simple version of the
/// Lengauer-Tarjan algorithm. There is another version that has an even better
/// theoretical running time of **O(|E| α(|E|, |V|))** where **α** is a
/// functional inverse of Ackermann's function. However, "Finding Dominators in
/// Practice" found it to be slower than the simpler version for all graphs they
/// tested:
///
/// > Both versions of the Lengauer-Tarjan algorithm (LT [the advanced version])
/// > and (SLT [the simple version]) are more robust [than the "Simple,
/// > Engineered" algorithm] on application graphs, and the advantage increases
/// > with graph size or graph complexity. Among these three, LT was the slowest,
/// > in contrast with the results reported by Lengauer and Tarjan [30]. SLT and
/// > [yet another dominators algorithm] were the most consistently fast
/// > algorithms in practice; since the former is less sensitive to pathological
/// > instances, we think it should be preferred where performance guarantees
/// > are important.
///
/// When should you choose `simple_fast` and when should you choose
/// `lengauer_tarjan`? As a rule of thumb, if lower memory usage is of utmost
/// importance to you, choose `simple_fast`. Otherwise, `lengauer_tarjan` is
/// usually a better choice.
///
/// However! Since both the `simple_fast` and `lengauer_tarjan` functions have
/// identical signatures, you can trivially try both and profile to see which is
/// better for you in practice.
///
/// [0]: http://www.cs.princeton.edu/courses/archive/spr03/cs423/download/dominators.pdf
/// [1]: http://jgaa.info/accepted/2006/GeorgiadisTarjanWerneck2006.10.1.pdf
///
/// ### Panics
///
/// Panics if the graph has `usize::MAX` vertices.
pub fn lengauer_tarjan<G>(graph: G, root: G::NodeId) -> Dominators<G::NodeId>
    where G: IntoNeighbors + Visitable,
          <G as GraphBase>::NodeId: ::std::fmt::Debug + Eq + Hash
{
    // The paper uses 1-based DFS numbering for vertices, but we use a 0-based
    // numbering to match with Rust's indexing.
    //
    // The reason the paper does that is because it is then free to use
    // `semis[w] == 0` as a sentinel for "not seen in this graph traversal yet".
    // However, since we are storing all auxiliary data in arrays indexed by DFS
    // numbering (which is much faster than hashing vertices all the time), we
    // don't know which index in `semis` to check until after the DFS numbering,
    // which means we can't use `semis` during the DFS numbering. Instead, we
    // keep a hash set of nodes we have seen, at the cost of some additional
    // memory overhead.

    // `parents[w]` is the parent of vertex `w` in the spanning tree.
    //
    // TODO: since `parents[w]` == `preds[w][0]` for all non-root `w`, we could
    // try special casing `preds[root]` and removing `parents` altogether. This
    // remains to be investigated.
    let mut parents = HashMap::new();

    // `preds[w]` is the set of vertices `v` such that there is an edge from `v`
    // to `w` in the graph.
    let mut preds = HashMap::new();

    // Contains different semantic data at different phases of the algorithm:
    //
    // * Before vertex `w` is numbered, `semis[w]` is past the end of the
    //   array. This differs from the paper; see the comment above about 0- vs
    //   1-based indexing for details.
    //
    // * After `w` is numbered but before its semi-dominator has been computed,
    //   `semis[w] == w`.
    //
    // * Once the semi-dominator for `w` is computed, `semis[w]` is the
    //   semi-dominator for `w`.
    let mut semis = vec![];

    // `vertices[i]` is the vertex that is numbered `i` in the DFS traversal.
    let mut vertices = vec![];

    // Step 1: Perform the DFS procedure from the paper, initializing our
    // auxiliary per-node data along the way.

    let mut stack = vec![root];
    let mut visited = HashMap::new();
    let mut seen: HashSet<G::NodeId> = HashSet::from_iter([root].iter().cloned());
    while let Some(node) = stack.pop() {
        let n = vertices.len();
        vertices.push(node);

        debug_assert_eq!(semis.len(), n);
        semis.push(n);

        debug_assert!(!visited.contains_key(&node));
        visited.insert(node, n);

        for successor in graph.neighbors(node) {
            if seen.insert(successor) {
                stack.push(successor);

                debug_assert!(!parents.contains_key(&successor));
                parents.insert(successor, node);
            }

            preds.entry(successor).or_insert(vec![]).push(node);
        }
    }

    // Because we use a 0-based DFS numbering, we have to use `usize::MAX` as
    // our sentinel in `compress` and `eval`, rather than `0` like the paper
    // does, to avoid doubling the size of `ancestors` (by making its type
    // `Vec<Option<usize>>`).
    assert!(vertices.len() < usize::max_value());

    debug_assert_eq!(visited[&root], 0, "The root is always index 0");
    debug_assert_eq!(visited.len(), seen.len());
    debug_assert_eq!(visited.len(), semis.len());
    debug_assert_eq!(visited.len(), vertices.len());
    debug_assert_eq!(
        visited.len() - 1,
        parents.len(),
        "Every vertex has a parent except for the root"
    );
    debug_assert!(
        preds.len() == vertices.len() || preds.len() == vertices.len() - 1,
        "Every non-root vertex must have at least one predecessor (its parent); \
         the root may or may not have a predecessor."
    );

    drop(seen);

    // Convert to vectors the hash maps that were hash maps only because we
    // didn't know the DFS numbering for some nodes yet. Accessing via DFS
    // number indexing is much faster than hash table lookups.

    let preds: Vec<Vec<_>> = vertices.iter()
        .map(|v| {
            preds.remove(v)
                .unwrap_or_else(|| {
                    debug_assert!(
                        *v == root,
                        "Only the root can potentially not have any predecessors"
                    );
                    vec![]
                })
                .into_iter()
                .map(|w| visited[&w])
                .collect()
        })
        .collect();

    let parents: Vec<_> = vertices.iter()
        .map(|v| {
            if *v == root {
                0
            } else {
                visited[&parents.remove(v).unwrap()]
            }
        })
        .collect();

    // `buckets[w]` contains the set of vertices whose semi-dominator is `w`.
    //
    // TODO: There is a trick we can do to avoid all these hash sets and their
    // heap allocations here: `buckets` can be implemented with two |V| arrays,
    // as described in the "Finding Dominators in Practice" paper. They found
    // that "in practice, avoiding unnecessary bucket insertions makes the
    // algorithm roughly 5% faster."
    let mut buckets = vec![HashSet::new(); vertices.len()];

    // Contains different semantic data at different phases of the algorithm:
    //
    // * After step 3, if `semis[w]` is the immediate dominator of `w`, then
    //   `doms[w]` is the immediate dominator of `w`. If `semis[w]` is not the
    //   immediate dominator of `w`, then `doms[w]` is a vertex `v` whose
    //   immediate dominator is also the immediate dominator of `w`.
    //
    // * After step 4, `doms[w]` is the immediate dominator of `w`.
    let mut doms = vec![0; vertices.len()];

    // Steps 2 and 3 happen simultaneously: we process the non-root vertices in
    // decreasing order, computing semi-dominators (step 2), and implicitly
    // defining immediate dominators (step 3). During these steps, we build and
    // maintain the forest contained within the DFS's spanning tree: the edges
    // `(parents[w], w)` for each vertex `w` that we've processed thus far.

    let mut ancestors = vec![usize::max_value(); vertices.len()];
    let mut labels: Vec<_> = (0..vertices.len()).collect();

    for w in (1..vertices.len()).rev() {
        // Step 2.
        for v in &preds[w] {
            let u = eval(*v, &mut ancestors, &mut labels, &semis);
            if semis[u] < semis[w] {
                semis[w] = semis[u];
            }
        }

        buckets[semis[w]].insert(w);
        link(parents[w], w, &mut ancestors);

        // Step 3.
        for v in buckets[parents[w]].drain() {
            let u = eval(v, &mut ancestors, &mut labels, &semis);
            doms[v] = if semis[u] < semis[v] {
                u
            } else {
                parents[w]
            };
        }
    }

    // Step 4: fill in immediate dominators that weren't explicitly defined by
    // step 3.
    for w in 1..vertices.len() {
        if doms[w] != semis[w] {
            doms[w] = doms[doms[w]];
        }
    }

    // The root dominates itself.
    debug_assert_eq!(doms[0], 0);

    // All done! Convert the indices back into nodes.
    Dominators {
        root: root,
        dominators: doms.into_iter()
            .enumerate()
            .map(|(idx, idom_idx)| (vertices[idx], vertices[idom_idx]))
            .collect(),
    }
}

// Performs path compression on the forest for `link` and `eval`.
fn compress(v: usize, ancestors: &mut [usize], labels: &mut [usize], semis: &[usize]) {
    debug_assert!(ancestors[v] != usize::max_value());

    if ancestors[ancestors[v]] != usize::max_value() {
        compress(ancestors[v], ancestors, labels, semis);

        if semis[labels[ancestors[v]]] < semis[labels[v]] {
            labels[v] = labels[ancestors[v]];
        }

        ancestors[v] = ancestors[ancestors[v]];
    }
}

// Add the edge `(v, w)` to the forest.
#[inline]
fn link(v: usize, w: usize, ancestors: &mut [usize]) {
    ancestors[w] = v;
}

// If `v` is the root for a tree in the forest, then return `v`. Otherwise,
// return the root of the tree in the forest which contains `v`.
fn eval(v: usize, ancestors: &mut [usize], labels: &mut [usize], semis: &[usize]) -> usize {
    if ancestors[v] == usize::max_value() {
        v
    } else {
        compress(v, ancestors, labels, semis);
        labels[v]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iter_dominators() {
        let doms: Dominators<u32> = Dominators {
            root: 0,
            dominators: [(2, 1), (1, 0), (0, 0)].iter().cloned().collect(),
        };

        let all_doms: Vec<_> = doms.dominators(2).unwrap().collect();
        assert_eq!(vec![2, 1, 0], all_doms);

        assert_eq!(None::<()>, doms.dominators(99).map(|_| unreachable!()));

        let strict_doms: Vec<_> = doms.strict_dominators(2).unwrap().collect();
        assert_eq!(vec![1, 0], strict_doms);

        assert_eq!(
            None::<()>,
            doms.strict_dominators(99).map(|_| unreachable!())
        );

        let dom_by: Vec<_> = doms.immediately_dominated_by(1).collect();
        assert_eq!(vec![2], dom_by);
        assert_eq!(None, doms.immediately_dominated_by(99).next());
    }
}
