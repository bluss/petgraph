extern crate petgraph;

#[cfg(feature="quickcheck")]
extern crate quickcheck;

use petgraph::{Graph, EdgeType, Directed, Undirected};
use petgraph::graph::{NodeIndex};
use petgraph::algo::{maximal_cliques};
use petgraph::visit::{GetAdjacencyMatrix, IntoNodeIdentifiers};

use std::collections::HashSet;
use std::hash::Hash;


/// Checks if a set of NodeIds are a clique, ie for all nodes a, b in the set, there is an edge
/// from a to b and b to a
fn is_clique<G>(g: G, clique: &HashSet<G::NodeId>) -> bool 
    where G: GetAdjacencyMatrix,
          G::NodeId: Eq + Hash,
{
    let matrix = g.adjacency_matrix();
    for &u in clique.iter() {
        for &v in clique.iter().filter(|&v| *v != u) {
            if !g.is_adjacent(&matrix, u, v) || !g.is_adjacent(&matrix, v, u) {
                return false;
            }
        }
    }
    return true;
}

/// checks if clique is maximal, ie there are no nodes in the graph such that there
/// exists a bidirectional edge between the node and every node and the clique
/// assumes g is a clique
fn is_maximal_clique<G>(g: G, clique: &HashSet<G::NodeId>) -> bool 
    where G: GetAdjacencyMatrix + IntoNodeIdentifiers,
          G::NodeId: Eq + Hash,
{
    let matrix = g.adjacency_matrix();
    for n in g.node_identifiers().filter(|n| !clique.contains(n)) {
        let mut connected_to_all = true;
        for &m in clique.iter() {
            if !g.is_adjacent(&matrix, n, m) || !g.is_adjacent(&matrix, m, n) {
                connected_to_all = false;
                break
            }
        }
        if connected_to_all {
            return false;
        }
    }
    return true;
}


#[test]
fn maximal_cliques_directed() {
    // 5 <- 3 = 4 == 0
    //      ||  || //
    //      2 <- 1
    let mut g = Graph::new();
    let a = g.add_node(0);
    let b = g.add_node(1);
    let c = g.add_node(2);
    let d = g.add_node(3);
    let e = g.add_node(4);
    let f = g.add_node(5);
    g.add_edge(a, b, ());
    g.add_edge(b, a, ());
    g.add_edge(a, e, ());
    g.add_edge(e, a, ());
    g.add_edge(b, e, ());
    g.add_edge(e, b, ());
    g.add_edge(b, c, ());
    g.add_edge(c, d, ());
    g.add_edge(d, c, ());
    g.add_edge(d, e, ());
    g.add_edge(e, d, ());
    g.add_edge(e, f, ());

    let cliques = maximal_cliques(&g);
    println!("{:?}", &cliques);
    let answer = vec![vec![a, b, e], vec![c, d], vec![d, e], vec![f]];
    for a in &answer {
        let s = a.iter().cloned().collect::<HashSet<NodeIndex>>();
        assert!(cliques.contains(&s));
    }
}

#[test]
fn maximal_cliques_undirected() {
    // 5 - 3 - 4 - 0
    //     |   | /
    //     2 - 1
    let mut g = Graph::new_undirected();
    let a = g.add_node(0);
    let b = g.add_node(1);
    let c = g.add_node(2);
    let d = g.add_node(3);
    let e = g.add_node(4);
    let f = g.add_node(5);
    g.add_edge(a, b, ());
    g.add_edge(a, e, ());
    g.add_edge(b, e, ());
    g.add_edge(b, c, ());
    g.add_edge(c, d, ());
    g.add_edge(d, e, ());
    g.add_edge(e, f, ());

    let cliques = maximal_cliques(&g);
    println!("{:?}", &cliques);
    let answer = vec![vec![a, b, e], vec![b, c], vec![c, d], vec![d, e], vec![e, f]];
    for a in &answer {
        let s = a.iter().cloned().collect::<HashSet<NodeIndex>>();
        assert!(cliques.contains(&s));
    }
}


#[cfg(feature="quickcheck")]
#[test]
fn prop_maximal_cliques_are_maximal_cliques() {
    fn prop<Ty>(g: Graph<(), (), Ty>) -> bool
        where Ty: EdgeType
    {
        if g.edge_count() <= 500 && g.node_count() <= 500 {

            let cliques = maximal_cliques(&g);
            for c in &cliques {
                if !is_clique(&g, &c) || !is_maximal_clique(&g, &c) {
                    println!("{:?}\n{:?}\n{:?}", &g, &c, &cliques);
                }
                assert!(is_clique(&g, &c));
                assert!(is_maximal_clique(&g, &c));
            }
        }
        true
    }
    quickcheck::quickcheck(prop as fn(Graph<_, _, Undirected>) -> bool);
    quickcheck::quickcheck(prop as fn(Graph<_, _, Directed>) -> bool);
}
