//! Graph algorithms.
//!
//! It is a goal to gradually migrate the algorithms to be based on graph traits
//! so that they are generally applicable. For now, some of these still require
//! the `Graph` type.

pub mod dominators;
mod test;

use std::cmp::min;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::hash::Hash;

use crate::prelude::*;

use super::graph::IndexType;
use super::unionfind::UnionFind;
use super::visit::{
    GetAdjacencyMatrix, GraphBase, GraphBase, GraphRef, GraphRef, 
    IntoEdgeReferences, IntoEdges, IntoNeighbors, IntoNeighborsDirected, 
    IntoNodeIdentifiers, NodeCompactIndexable, NodeCount, NodeIndexable, 
    Reversed, VisitMap, Visitable,
};
use super::EdgeType;
use crate::data::Element;
use crate::scored::MinScored;
use crate::visit::Walker;
use crate::visit::{Data, IntoNodeReferences, NodeRef};

pub use super::astar::astar;
pub use super::dijkstra::dijkstra;
pub use super::k_shortest_path::k_shortest_path;

pub use super::isomorphism::{is_isomorphic, is_isomorphic_matching};
pub use super::simple_paths::all_simple_paths;

/// \[Generic\] Return the number of connected components of the graph.
///
/// For a directed graph, this is the *weakly* connected components.
/// # Example
/// ```rust
/// use petgraph::Graph;
/// use petgraph::algo::connected_components;
/// use petgraph::prelude::*;
///
/// let mut graph : Graph<(),(),Directed>= Graph::new();
/// let a = graph.add_node(()); // node with no weight
/// let b = graph.add_node(());
/// let c = graph.add_node(());
/// let d = graph.add_node(());
/// let e = graph.add_node(());
/// let f = graph.add_node(());
/// let g = graph.add_node(());
/// let h = graph.add_node(());
///
/// graph.extend_with_edges(&[
///     (a, b),
///     (b, c),
///     (c, d),
///     (d, a),
///     (e, f),
///     (f, g),
///     (g, h),
///     (h, e)
/// ]);
/// // a ----> b       e ----> f
/// // ^       |       ^       |
/// // |       v       |       v
/// // d <---- c       h <---- g
///
/// assert_eq!(connected_components(&graph),2);
/// graph.add_edge(b,e,());
/// assert_eq!(connected_components(&graph),1);
/// ```
pub fn connected_components<G>(g: G) -> usize
where
    G: NodeCompactIndexable + IntoEdgeReferences,
{
    let mut vertex_sets = UnionFind::new(g.node_bound());
    for edge in g.edge_references() {
        let (a, b) = (edge.source(), edge.target());

        // union the two vertices of the edge
        vertex_sets.union(g.to_index(a), g.to_index(b));
    }
    let mut labels = vertex_sets.into_labeling();
    labels.sort();
    labels.dedup();
    labels.len()
}

/// \[Generic\] Return `true` if the input graph contains a cycle.
///
/// Always treats the input graph as if undirected.
pub fn is_cyclic_undirected<G>(g: G) -> bool
where
    G: NodeIndexable + IntoEdgeReferences,
{
    let mut edge_sets = UnionFind::new(g.node_bound());
    for edge in g.edge_references() {
        let (a, b) = (edge.source(), edge.target());

        // union the two vertices of the edge
        //  -- if they were already the same, then we have a cycle
        if !edge_sets.union(g.to_index(a), g.to_index(b)) {
            return true;
        }
    }
    false
}

/// \[Generic\] Perform a topological sort of a directed graph.
///
/// If the graph was acyclic, return a vector of nodes in topological order:
/// each node is ordered before its successors.
/// Otherwise, it will return a `Cycle` error. Self loops are also cycles.
///
/// To handle graphs with cycles, use the scc algorithms or `DfsPostOrder`
/// instead of this function.
///
/// If `space` is not `None`, it is used instead of creating a new workspace for
/// graph traversal. The implementation is iterative.
pub fn toposort<G>(
    g: G,
    space: Option<&mut DfsSpace<G::NodeId, G::Map>>,
) -> Result<Vec<G::NodeId>, Cycle<G::NodeId>>
where
    G: IntoNeighborsDirected + IntoNodeIdentifiers + Visitable,
{
    // based on kosaraju scc
    with_dfs(g, space, |dfs| {
        dfs.reset(g);
        let mut finished = g.visit_map();

        let mut finish_stack = Vec::new();
        for i in g.node_identifiers() {
            if dfs.discovered.is_visited(&i) {
                continue;
            }
            dfs.stack.push(i);
            while let Some(&nx) = dfs.stack.last() {
                if dfs.discovered.visit(nx) {
                    // First time visiting `nx`: Push neighbors, don't pop `nx`
                    for succ in g.neighbors(nx) {
                        if succ == nx {
                            // self cycle
                            return Err(Cycle(nx));
                        }
                        if !dfs.discovered.is_visited(&succ) {
                            dfs.stack.push(succ);
                        }
                    }
                } else {
                    dfs.stack.pop();
                    if finished.visit(nx) {
                        // Second time: All reachable nodes must have been finished
                        finish_stack.push(nx);
                    }
                }
            }
        }
        finish_stack.reverse();

        dfs.reset(g);
        for &i in &finish_stack {
            dfs.move_to(i);
            let mut cycle = false;
            while let Some(j) = dfs.next(Reversed(g)) {
                if cycle {
                    return Err(Cycle(j));
                }
                cycle = true;
            }
        }

        Ok(finish_stack)
    })
}

/// \[Generic\] Return `true` if the input directed graph contains a cycle.
///
/// This implementation is recursive; use `toposort` if an alternative is
/// needed.
pub fn is_cyclic_directed<G>(g: G) -> bool
where
    G: IntoNodeIdentifiers + IntoNeighbors + Visitable,
{
    use crate::visit::{depth_first_search, DfsEvent};

    depth_first_search(g, g.node_identifiers(), |event| match event {
        DfsEvent::BackEdge(_, _) => Err(()),
        _ => Ok(()),
    })
    .is_err()
}

type DfsSpaceType<G> = DfsSpace<<G as GraphBase>::NodeId, <G as Visitable>::Map>;

/// Workspace for a graph traversal.
#[derive(Clone, Debug)]
pub struct DfsSpace<N, VM> {
    dfs: Dfs<N, VM>,
}

impl<N, VM> DfsSpace<N, VM>
where
    N: Copy + PartialEq,
    VM: VisitMap<N>,
{
    pub fn new<G>(g: G) -> Self
    where
        G: GraphRef + Visitable<NodeId = N, Map = VM>,
    {
        DfsSpace { dfs: Dfs::empty(g) }
    }
}

impl<N, VM> Default for DfsSpace<N, VM>
where
    VM: VisitMap<N> + Default,
{
    fn default() -> Self {
        DfsSpace {
            dfs: Dfs {
                stack: <_>::default(),
                discovered: <_>::default(),
            },
        }
    }
}

/// Create a Dfs if it's needed
fn with_dfs<G, F, R>(g: G, space: Option<&mut DfsSpaceType<G>>, f: F) -> R
where
    G: GraphRef + Visitable,
    F: FnOnce(&mut Dfs<G::NodeId, G::Map>) -> R,
{
    let mut local_visitor;
    let dfs = if let Some(v) = space {
        &mut v.dfs
    } else {
        local_visitor = Dfs::empty(g);
        &mut local_visitor
    };
    f(dfs)
}

/// \[Generic\] Check if there exists a path starting at `from` and reaching `to`.
///
/// If `from` and `to` are equal, this function returns true.
///
/// If `space` is not `None`, it is used instead of creating a new workspace for
/// graph traversal.
pub fn has_path_connecting<G>(
    g: G,
    from: G::NodeId,
    to: G::NodeId,
    space: Option<&mut DfsSpace<G::NodeId, G::Map>>,
) -> bool
where
    G: IntoNeighbors + Visitable,
{
    with_dfs(g, space, |dfs| {
        dfs.reset(g);
        dfs.move_to(from);
        dfs.iter(g).any(|x| x == to)
    })
}

/// Renamed to `kosaraju_scc`.
#[deprecated(note = "renamed to kosaraju_scc")]
pub fn scc<G>(g: G) -> Vec<Vec<G::NodeId>>
where
    G: IntoNeighborsDirected + Visitable + IntoNodeIdentifiers,
{
    kosaraju_scc(g)
}

/// \[Generic\] Compute the *strongly connected components* using [Kosaraju's algorithm][1].
///
/// [1]: https://en.wikipedia.org/wiki/Kosaraju%27s_algorithm
///
/// Return a vector where each element is a strongly connected component (scc).
/// The order of node ids within each scc is arbitrary, but the order of
/// the sccs is their postorder (reverse topological sort).
///
/// For an undirected graph, the sccs are simply the connected components.
///
/// This implementation is iterative and does two passes over the nodes.
pub fn kosaraju_scc<G>(g: G) -> Vec<Vec<G::NodeId>>
where
    G: IntoNeighborsDirected + Visitable + IntoNodeIdentifiers,
{
    let mut dfs = DfsPostOrder::empty(g);

    // First phase, reverse dfs pass, compute finishing times.
    // http://stackoverflow.com/a/26780899/161659
    let mut finish_order = Vec::with_capacity(0);
    for i in g.node_identifiers() {
        if dfs.discovered.is_visited(&i) {
            continue;
        }

        dfs.move_to(i);
        while let Some(nx) = dfs.next(Reversed(g)) {
            finish_order.push(nx);
        }
    }

    let mut dfs = Dfs::from_parts(dfs.stack, dfs.discovered);
    dfs.reset(g);
    let mut sccs = Vec::new();

    // Second phase
    // Process in decreasing finishing time order
    for i in finish_order.into_iter().rev() {
        if dfs.discovered.is_visited(&i) {
            continue;
        }
        // Move to the leader node `i`.
        dfs.move_to(i);
        let mut scc = Vec::new();
        while let Some(nx) = dfs.next(g) {
            scc.push(nx);
        }
        sccs.push(scc);
    }
    sccs
}

#[derive(Copy, Clone, Debug)]
struct NodeData {
    index: Option<usize>,
    lowlink: usize,
    on_stack: bool,
}

/// A reusable state for computing the *strongly connected components* using [Tarjan's algorithm][1].
///
/// [1]: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
#[derive(Debug)]
pub struct TarjanScc<N> {
    index: usize,
    nodes: Vec<NodeData>,
    stack: Vec<N>,
}

impl<N> Default for TarjanScc<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N> TarjanScc<N> {
    /// Creates a new `TarjanScc`
    pub fn new() -> Self {
        TarjanScc {
            index: 0,
            nodes: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// \[Generic\] Compute the *strongly connected components* using [Tarjan's algorithm][1].
    ///
    /// [1]: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
    ///
    /// Calls `f` for each strongly strongly connected component (scc).
    /// The order of node ids within each scc is arbitrary, but the order of
    /// the sccs is their postorder (reverse topological sort).
    ///
    /// For an undirected graph, the sccs are simply the connected components.
    ///
    /// This implementation is recursive and does one pass over the nodes.
    pub fn run<G, F>(&mut self, g: G, mut f: F)
    where
        G: IntoNodeIdentifiers<NodeId = N> + IntoNeighbors<NodeId = N> + NodeIndexable<NodeId = N>,
        F: FnMut(&[N]),
        N: Copy + PartialEq,
    {
        self.nodes.clear();
        self.nodes.resize(
            g.node_bound(),
            NodeData {
                index: None,
                lowlink: !0,
                on_stack: false,
            },
        );

        for n in g.node_identifiers() {
            self.visit(n, g, &mut f);
        }

        debug_assert!(self.stack.is_empty());
    }

    fn visit<G, F>(&mut self, v: G::NodeId, g: G, f: &mut F)
    where
        G: IntoNeighbors<NodeId = N> + NodeIndexable<NodeId = N>,
        F: FnMut(&[N]),
        N: Copy + PartialEq,
    {
        macro_rules! node {
            ($node:expr) => {
                self.nodes[g.to_index($node)]
            };
        }

        let node_v = &mut node![v];
        if node_v.index.is_some() {
            // already visited
            return;
        }

        let v_index = self.index;
        node_v.index = Some(v_index);
        node_v.lowlink = v_index;
        node_v.on_stack = true;
        self.stack.push(v);
        self.index += 1;

        for w in g.neighbors(v) {
            let node_w = &mut node![w];
            match node_w.index {
                None => {
                    self.visit(w, g, f);
                    node![v].lowlink = min(node![v].lowlink, node![w].lowlink);
                }
                Some(w_index) => {
                    if node_w.on_stack {
                        // Successor w is in stack S and hence in the current SCC
                        let v_lowlink = &mut node![v].lowlink;
                        *v_lowlink = min(*v_lowlink, w_index);
                    }
                }
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        let node_v = &mut node![v];
        if let Some(v_index) = node_v.index {
            if node_v.lowlink == v_index {
                let nodes = &mut self.nodes;
                let start = self
                    .stack
                    .iter()
                    .rposition(|&w| {
                        nodes[g.to_index(w)].on_stack = false;
                        g.to_index(w) == g.to_index(v)
                    })
                    .unwrap();
                f(&self.stack[start..]);
                self.stack.truncate(start);
            }
        }
    }
}

/// \[Generic\] Compute the *strongly connected components* using [Tarjan's algorithm][1].
///
/// [1]: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
///
/// Return a vector where each element is a strongly connected component (scc).
/// The order of node ids within each scc is arbitrary, but the order of
/// the sccs is their postorder (reverse topological sort).
///
/// For an undirected graph, the sccs are simply the connected components.
///
/// This implementation is recursive and does one pass over the nodes.
pub fn tarjan_scc<G>(g: G) -> Vec<Vec<G::NodeId>>
where
    G: IntoNodeIdentifiers + IntoNeighbors + NodeIndexable,
{
    let mut sccs = Vec::new();
    {
        let mut tarjan_scc = TarjanScc::new();
        tarjan_scc.run(g, |scc| sccs.push(scc.iter().cloned().rev().collect()));
    }
    sccs
}

/// [Graph] Condense every strongly connected component into a single node and return the result.
///
/// If `make_acyclic` is true, self-loops and multi edges are ignored, guaranteeing that
/// the output is acyclic.
/// # Example
/// ```rust
/// use petgraph::Graph;
/// use petgraph::algo::condensation;
/// use petgraph::prelude::*;
///
/// let mut graph : Graph<(),(),Directed> = Graph::new();
/// let a = graph.add_node(()); // node with no weight
/// let b = graph.add_node(());
/// let c = graph.add_node(());
/// let d = graph.add_node(());
/// let e = graph.add_node(());
/// let f = graph.add_node(());
/// let g = graph.add_node(());
/// let h = graph.add_node(());
///
/// graph.extend_with_edges(&[
///     (a, b),
///     (b, c),
///     (c, d),
///     (d, a),
///     (b, e),
///     (e, f),
///     (f, g),
///     (g, h),
///     (h, e)
/// ]);
///
/// // a ----> b ----> e ----> f
/// // ^       |       ^       |
/// // |       v       |       v
/// // d <---- c       h <---- g
///
/// let condensed_graph = condensation(graph,false);
/// let A = NodeIndex::new(0);
/// let B = NodeIndex::new(1);
/// assert_eq!(condensed_graph.node_count(), 2);
/// assert_eq!(condensed_graph.edge_count(), 9);
/// assert_eq!(condensed_graph.neighbors(A).collect::<Vec<_>>(), vec![A, A, A, A]);
/// assert_eq!(condensed_graph.neighbors(B).collect::<Vec<_>>(), vec![A, B, B, B, B]);
/// ```
/// If `make_acyclic` is true, self-loops and multi edges are ignored:
///
/// ```rust
/// # use petgraph::Graph;
/// # use petgraph::algo::condensation;
/// # use petgraph::prelude::*;
/// #
/// # let mut graph : Graph<(),(),Directed> = Graph::new();
/// # let a = graph.add_node(()); // node with no weight
/// # let b = graph.add_node(());
/// # let c = graph.add_node(());
/// # let d = graph.add_node(());
/// # let e = graph.add_node(());
/// # let f = graph.add_node(());
/// # let g = graph.add_node(());
/// # let h = graph.add_node(());
/// #
/// # graph.extend_with_edges(&[
/// #    (a, b),
/// #    (b, c),
/// #    (c, d),
/// #    (d, a),
/// #    (b, e),
/// #    (e, f),
/// #    (f, g),
/// #    (g, h),
/// #    (h, e)
/// # ]);
/// let acyclic_condensed_graph = condensation(graph, true);
/// let A = NodeIndex::new(0);
/// let B = NodeIndex::new(1);
/// assert_eq!(acyclic_condensed_graph.node_count(), 2);
/// assert_eq!(acyclic_condensed_graph.edge_count(), 1);
/// assert_eq!(acyclic_condensed_graph.neighbors(B).collect::<Vec<_>>(), vec![A]);
/// ```
pub fn condensation<N, E, Ty, Ix>(
    g: Graph<N, E, Ty, Ix>,
    make_acyclic: bool,
) -> Graph<Vec<N>, E, Ty, Ix>
where
    Ty: EdgeType,
    Ix: IndexType,
{
    let sccs = kosaraju_scc(&g);
    let mut condensed: Graph<Vec<N>, E, Ty, Ix> = Graph::with_capacity(sccs.len(), g.edge_count());

    // Build a map from old indices to new ones.
    let mut node_map = vec![NodeIndex::end(); g.node_count()];
    for comp in sccs {
        let new_nix = condensed.add_node(Vec::new());
        for nix in comp {
            node_map[nix.index()] = new_nix;
        }
    }

    // Consume nodes and edges of the old graph and insert them into the new one.
    let (nodes, edges) = g.into_nodes_edges();
    for (nix, node) in nodes.into_iter().enumerate() {
        condensed[node_map[nix]].push(node.weight);
    }
    for edge in edges {
        let source = node_map[edge.source().index()];
        let target = node_map[edge.target().index()];
        if make_acyclic {
            if source != target {
                condensed.update_edge(source, target, edge.weight);
            }
        } else {
            condensed.add_edge(source, target, edge.weight);
        }
    }
    condensed
}

/// \[Generic\] Compute a *minimum spanning tree* of a graph.
///
/// The input graph is treated as if undirected.
///
/// Using Kruskal's algorithm with runtime **O(|E| log |E|)**. We actually
/// return a minimum spanning forest, i.e. a minimum spanning tree for each connected
/// component of the graph.
///
/// The resulting graph has all the vertices of the input graph (with identical node indices),
/// and **|V| - c** edges, where **c** is the number of connected components in `g`.
///
/// Use `from_elements` to create a graph from the resulting iterator.
pub fn min_spanning_tree<G>(g: G) -> MinSpanningTree<G>
where
    G::NodeWeight: Clone,
    G::EdgeWeight: Clone + PartialOrd,
    G: IntoNodeReferences + IntoEdgeReferences + NodeIndexable,
{
    // Initially each vertex is its own disjoint subgraph, track the connectedness
    // of the pre-MST with a union & find datastructure.
    let subgraphs = UnionFind::new(g.node_bound());

    let edges = g.edge_references();
    let mut sort_edges = BinaryHeap::with_capacity(edges.size_hint().0);
    for edge in edges {
        sort_edges.push(MinScored(
            edge.weight().clone(),
            (edge.source(), edge.target()),
        ));
    }

    MinSpanningTree {
        graph: g,
        node_ids: Some(g.node_references()),
        subgraphs,
        sort_edges,
        node_map: HashMap::new(),
        node_count: 0,
    }
}

/// An iterator producing a minimum spanning forest of a graph.
pub struct MinSpanningTree<G>
where
    G: Data + IntoNodeReferences,
{
    graph: G,
    node_ids: Option<G::NodeReferences>,
    subgraphs: UnionFind<usize>,
    sort_edges: BinaryHeap<MinScored<G::EdgeWeight, (G::NodeId, G::NodeId)>>,
    node_map: HashMap<usize, usize>,
    node_count: usize,
}

impl<G> Iterator for MinSpanningTree<G>
where
    G: IntoNodeReferences + NodeIndexable,
    G::NodeWeight: Clone,
    G::EdgeWeight: PartialOrd,
{
    type Item = Element<G::NodeWeight, G::EdgeWeight>;

    fn next(&mut self) -> Option<Self::Item> {
        let g = self.graph;
        if let Some(ref mut iter) = self.node_ids {
            if let Some(node) = iter.next() {
                self.node_map.insert(g.to_index(node.id()), self.node_count);
                self.node_count += 1;
                return Some(Element::Node {
                    weight: node.weight().clone(),
                });
            }
        }
        self.node_ids = None;

        // Kruskal's algorithm.
        // Algorithm is this:
        //
        // 1. Create a pre-MST with all the vertices and no edges.
        // 2. Repeat:
        //
        //  a. Remove the shortest edge from the original graph.
        //  b. If the edge connects two disjoint trees in the pre-MST,
        //     add the edge.
        while let Some(MinScored(score, (a, b))) = self.sort_edges.pop() {
            // check if the edge would connect two disjoint parts
            let (a_index, b_index) = (g.to_index(a), g.to_index(b));
            if self.subgraphs.union(a_index, b_index) {
                let (&a_order, &b_order) =
                    match (self.node_map.get(&a_index), self.node_map.get(&b_index)) {
                        (Some(a_id), Some(b_id)) => (a_id, b_id),
                        _ => panic!("Edge references unknown node"),
                    };
                return Some(Element::Edge {
                    source: a_order,
                    target: b_order,
                    weight: score,
                });
            }
        }
        None
    }
}

/// An algorithm error: a cycle was found in the graph.
#[derive(Clone, Debug, PartialEq)]
pub struct Cycle<N>(N);

impl<N> Cycle<N> {
    /// Return a node id that participates in the cycle
    pub fn node_id(&self) -> N
    where
        N: Copy,
    {
        self.0
    }
}
/// An algorithm error: a cycle of negative weights was found in the graph.
#[derive(Clone, Debug, PartialEq)]
pub struct NegativeCycle(());

/// \[Generic\] Compute shortest paths from node `source` to all other.
///
/// Using the [Bellman–Ford algorithm][bf]; negative edge costs are
/// permitted, but the graph must not have a cycle of negative weights
/// (in that case it will return an error).
///
/// On success, return one vec with path costs, and another one which points
/// out the predecessor of a node along a shortest path. The vectors
/// are indexed by the graph's node indices.
///
/// [bf]: https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm
///
/// # Example
/// ```rust
/// use petgraph::Graph;
/// use petgraph::algo::bellman_ford;
/// use petgraph::prelude::*;
///
/// let mut g = Graph::new();
/// let a = g.add_node(()); // node with no weight
/// let b = g.add_node(());
/// let c = g.add_node(());
/// let d = g.add_node(());
/// let e = g.add_node(());
/// let f = g.add_node(());
/// g.extend_with_edges(&[
///     (0, 1, 2.0),
///     (0, 3, 4.0),
///     (1, 2, 1.0),
///     (1, 5, 7.0),
///     (2, 4, 5.0),
///     (4, 5, 1.0),
///     (3, 4, 1.0),
/// ]);
///
/// // Graph represented with the weight of each edge
/// //
/// //     2       1
/// // a ----- b ----- c
/// // | 4     | 7     |
/// // d       f       | 5
/// // | 1     | 1     |
/// // \------ e ------/
///
/// let path = bellman_ford(&g, a);
/// assert_eq!(path, Ok((vec![0.0 ,     2.0,    3.0,    4.0,     5.0,     6.0],
///                      vec![None, Some(a),Some(b),Some(a), Some(d), Some(e)]
///                    ))
///           );
/// // Node f (indice 5) can be reach from a with a path costing 6.
/// // Predecessor of f is Some(e) which predecessor is Some(d) which predecessor is Some(a).
/// // Thus the path from a to f is a <-> d <-> e <-> f
///
/// let graph_with_neg_cycle = Graph::<(), f32, Undirected>::from_edges(&[
///         (0, 1, -2.0),
///         (0, 3, -4.0),
///         (1, 2, -1.0),
///         (1, 5, -25.0),
///         (2, 4, -5.0),
///         (4, 5, -25.0),
///         (3, 4, -1.0),
/// ]);
///
/// assert!(bellman_ford(&graph_with_neg_cycle, NodeIndex::new(0)).is_err());
/// ```
pub fn bellman_ford<G>(
    g: G,
    source: G::NodeId,
) -> Result<(Vec<G::EdgeWeight>, Vec<Option<G::NodeId>>), NegativeCycle>
where
    G: NodeCount + IntoNodeIdentifiers + IntoEdges + NodeIndexable,
    G::EdgeWeight: FloatMeasure,
{
    let mut predecessor = vec![None; g.node_bound()];
    let mut distance = vec![<_>::infinite(); g.node_bound()];

    let ix = |i| g.to_index(i);

    distance[ix(source)] = <_>::zero();
    // scan up to |V| - 1 times.
    for _ in 1..g.node_count() {
        let mut did_update = false;
        for i in g.node_identifiers() {
            for edge in g.edges(i) {
                let i = edge.source();
                let j = edge.target();
                let w = *edge.weight();
                if distance[ix(i)] + w < distance[ix(j)] {
                    distance[ix(j)] = distance[ix(i)] + w;
                    predecessor[ix(j)] = Some(i);
                    did_update = true;
                }
            }
        }
        if !did_update {
            break;
        }
    }

    // check for negative weight cycle
    for i in g.node_identifiers() {
        for edge in g.edges(i) {
            let j = edge.target();
            let w = *edge.weight();
            if distance[ix(i)] + w < distance[ix(j)] {
                //println!("neg cycle, detected from {} to {}, weight={}", i, j, w);
                return Err(NegativeCycle(()));
            }
        }
    }

    Ok((distance, predecessor))
}

/// Return `true` if the graph is bipartite. A graph is bipartite if it's nodes can be divided into
/// two disjoint and indepedent sets U and V such that every edge connects U to one in V. This
/// algorithm implements 2-coloring algorithm based on the BFS algorithm.
///
/// Always treats the input graph as if undirected.
pub fn is_bipartite_undirected<G, N, VM>(g: G, start: N) -> bool
where
    G: GraphRef + Visitable<NodeId = N, Map = VM> + IntoNeighbors<NodeId = N>,
    N: Copy + PartialEq + std::fmt::Debug,
    VM: VisitMap<N>,
{
    let mut red = g.visit_map();
    red.visit(start);
    let mut blue = g.visit_map();

    let mut stack = ::std::collections::VecDeque::new();
    stack.push_front(start);

    while let Some(node) = stack.pop_front() {
        let is_red = red.is_visited(&node);
        let is_blue = blue.is_visited(&node);

        assert!(is_red ^ is_blue);

        for neighbour in g.neighbors(node) {
            let is_neigbour_red = red.is_visited(&neighbour);
            let is_neigbour_blue = blue.is_visited(&neighbour);

            if (is_red && is_neigbour_red) || (is_blue && is_neigbour_blue) {
                return false;
            }

            if !is_neigbour_red && !is_neigbour_blue {
                //hasn't been visited yet

                match (is_red, is_blue) {
                    (true, false) => {
                        blue.visit(neighbour);
                    }
                    (false, true) => {
                        red.visit(neighbour);
                    }
                    (_, _) => {
                        panic!("Invariant doesn't hold");
                    }
                }

                stack.push_back(neighbour);
            }
        }
    }

    true
}

use std::fmt::Debug;
use std::ops::Add;

/// Associated data that can be used for measures (such as length).
pub trait Measure: Debug + PartialOrd + Add<Self, Output = Self> + Default + Clone {}

impl<M> Measure for M where M: Debug + PartialOrd + Add<M, Output = M> + Default + Clone {}

/// A floating-point measure.
pub trait FloatMeasure: Measure + Copy {
    fn zero() -> Self;
    fn infinite() -> Self;
}

impl FloatMeasure for f32 {
    fn zero() -> Self {
        0.
    }
    fn infinite() -> Self {
        1. / 0.
    }
}

impl FloatMeasure for f64 {
    fn zero() -> Self {
        0.
    }
    fn infinite() -> Self {
        1. / 0.
    }
}


/// Finds maximal cliques containing all the vertices in r, some of the
/// vertices in p, and none of the vertices in x.
fn bron_kerbosch_pivot<G>(g: G,
                            adj_mat: &G::AdjMatrix,
                            r: HashSet<G::NodeId>,
                            mut p: HashSet<G::NodeId>,
                            mut x: HashSet<G::NodeId>)
    -> Vec<HashSet<G::NodeId>>
    where G: GetAdjacencyMatrix,
          G: IntoNeighbors,
          G::NodeId: Eq + Hash,
{
    let mut cliques = Vec::with_capacity(1);
    if p.is_empty() {
        if x.is_empty() {
            cliques.push(r);
        }
        return cliques;
    }
    let u = //pick pivot to be vertex with max degree
    {
        let mut max_deg = 0;
        let mut max_vtx = None;
        for &v in &p {
            let c = g.neighbors(v).count();
            if max_vtx.is_none() || c > max_deg {
                max_deg = c;
                max_vtx = Some(v);
            }
        }
        max_vtx.unwrap()
    };
    let mut todo = p.iter()
        .filter(|&v| (u == *v ||
            !g.is_adjacent(adj_mat, u, *v) ||
            !g.is_adjacent(adj_mat, *v, u))) //skip neighbors of pivot
        .cloned()
        .collect::<Vec<G::NodeId>>();
    while let Some(v) = todo.pop() {
        let mut neighbors = HashSet::new();
        let mut walker = g.neighbors(v);
        while let Some(w) = walker.next() { //filter
            if g.is_adjacent(adj_mat, w, v) {
                neighbors.insert(w);
            }
        }
        p.remove(&v);
        let mut next_r = r.clone();
        next_r.insert(v);

        let next_p = p.intersection(&neighbors).cloned().collect::<HashSet<G::NodeId>>();
        let next_x = x.intersection(&neighbors).cloned().collect::<HashSet<G::NodeId>>();

        cliques.extend(bron_kerbosch_pivot(g, adj_mat, next_r, next_p, next_x));

        x.insert(v);
    }

    return cliques;
}


/// Find all maximal cliques in a graph
pub fn maximal_cliques<G>(g: G) -> Vec<HashSet<G::NodeId>>
    where G: GetAdjacencyMatrix,
          G: IntoNodeIdentifiers + IntoNeighbors,
          G::NodeId: Eq + Hash,
{
    let r = HashSet::new();
    let p = g.node_identifiers().collect::<HashSet<G::NodeId>>();
    let x = HashSet::new();
    let adj_mat = g.adjacency_matrix();
    return bron_kerbosch_pivot(g, &adj_mat, r, p, x);
}

/// (reference implementation)
/// Finds maximal cliques containing all the vertices in r, some of the
/// vertices in p, and none of the vertices in x.
#[allow(dead_code)] //used by tests
fn bron_kerbosch_ref<G>(g: G,
                            adj_mat: &G::AdjMatrix,
                            r: HashSet<G::NodeId>,
                            mut p: HashSet<G::NodeId>,
                            mut x: HashSet<G::NodeId>)
    -> Vec<HashSet<G::NodeId>>
    where G: GetAdjacencyMatrix,
          G: IntoNeighbors,
          G::NodeId: Eq + Hash,
{
    let mut cliques = Vec::with_capacity(1);
    if p.is_empty() && x.is_empty() {
        cliques.push(r);
        return cliques;
    }
    let mut todo = p.iter().cloned().collect::<Vec<G::NodeId>>();
    while let Some(v) = todo.pop() {
        p.remove(&v);
        let mut next_r = r.clone();
        next_r.insert(v);

        let mut neighbors = HashSet::new();
        let mut walker = g.neighbors(v);
        while let Some(u) = walker.next() {
            if g.is_adjacent(adj_mat, u, v) {
                neighbors.insert(u);
            }
        }

        let next_p = p.intersection(&neighbors).cloned().collect::<HashSet<G::NodeId>>();
        let next_x = x.intersection(&neighbors).cloned().collect::<HashSet<G::NodeId>>();

        cliques.extend(bron_kerbosch_ref(g, adj_mat, next_r, next_p, next_x));

        x.insert(v);
    }
    return cliques;
}

/// (reference implementation)
/// Find all maximal cliques in a graph.
#[allow(dead_code)] //used by tests
fn maximal_cliques_ref<G>(g: G) -> Vec<HashSet<G::NodeId>>
    where G: GetAdjacencyMatrix,
          G: IntoNodeIdentifiers + IntoNeighbors,
          G::NodeId: Eq + Hash,
{
    let adj_mat = g.adjacency_matrix();
    let p = g.node_identifiers().collect::<HashSet<G::NodeId>>();
    return bron_kerbosch_ref(g, &adj_mat, HashSet::new(), p, HashSet::new());
}
