use std::collections::HashMap;

use std::hash::Hash;

use super::visit::{EdgeRef, IntoEdges, IntoNodeIdentifiers};

/// \[Generic\] modularity computation of a Graph G with given partition.
///
///
/// The graph should implement `IntoEdges` and `IntoNodeIdentifiers`. The function
/// `node_community` should return the community for a particular node, which is used
/// to compute the modularity.
///
/// For an undirected graph, every edge is treaten as two direct edges.
///
/// Returns the modularity of the Graph.
/// # Example
/// ```rust
/// use petgraph::Graph;
/// use petgraph::algo::modularity;
/// use petgraph::prelude::*;
///
/// let mut graph : UnGraph<(),()>= Graph::new_undirected();
/// let a = graph.add_node(()); // node with no weight
/// let b = graph.add_node(());
/// let c = graph.add_node(());
/// let d = graph.add_node(());
/// let e = graph.add_node(());
/// let f = graph.add_node(());
///
/// graph.extend_with_edges(&[
///     (a, b),
///     (b, c),
///     (c, a),
///     (d, b),
///     (d, e),
///     (e, f),
///     (f, d),
/// ]);
/// // a - b ---- d - e
/// //  \  |       \  |
/// //   \ |        \ |
/// //     c          f
///
/// let expected_res = 0.3571428571428571;
/// let res = modularity(&graph, |node| if node == a || node == b || node == c { 1 } else { 0 });
/// assert_eq!(res, expected_res);
/// ```
pub fn modularity<G, F, K>(graph: G, mut node_community: F) -> f64
where
    G: IntoEdges + IntoNodeIdentifiers,
    G::NodeId: Eq,
    F: FnMut(G::NodeId) -> K,
    K: Eq + Hash,
{
    let mut map: HashMap<K, (usize, usize)> = HashMap::new();
    let mut sum_edges = 0;
    for node in graph.node_identifiers() {
        let community = node_community(node);
        let mut degree = 0;
        let mut intra_community_edges = 0;
        for edge in graph.edges(node) {
            sum_edges += 1;
            let next = node_community(edge.target());
            if community == next {
                intra_community_edges += 1;
                degree += 2;
            } else {
                degree += 1;
                let entry = map.entry(next).or_insert((0, 0));
                *entry = (entry.0, entry.1 + 1);
            }
        }
        let entry = map.entry(community).or_insert((0, 0));
        *entry = (entry.0 + intra_community_edges, entry.1 + degree);
    }

    let m = sum_edges as f64;
    map.iter()
        .map(|(_, (x, y))| (*x as f64, *y as f64))
        .map(|(lc, kc)| lc / m - (kc / (2.0 * m)).powf(2.0))
        .sum()
}
