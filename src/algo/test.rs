#![cfg(test)]

#[cfg(feature="quickcheck")]
extern crate quickcheck;

use std::collections::HashSet;

use super::{maximal_cliques, maximal_cliques_ref};
use super::super::graph::{Graph, NodeIndex};
use super::super::{Directed, Undirected, EdgeType};


#[test]
fn maximal_cliques_ref_directed() {
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

    let cliques = maximal_cliques_ref(&g);
    println!("{:?}", &cliques);
    let answer = vec![vec![a, b, e], vec![c, d], vec![d, e], vec![f]];
    for a in &answer {
        let s = a.iter().cloned().collect::<HashSet<NodeIndex>>();
        assert!(cliques.contains(&s));
    }
}

#[test]
fn maximal_cliques_ref_undirected() {
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

    let cliques = maximal_cliques_ref(&g);
    println!("{:?}", &cliques);
    let answer = vec![vec![a, b, e], vec![b, c], vec![c, d], vec![d, e], vec![e, f]];
    for a in &answer {
        let s = a.iter().cloned().collect::<HashSet<NodeIndex>>();
        assert!(cliques.contains(&s));
    }
}


#[cfg(feature="quickcheck")]
#[test]
fn maximal_cliques_matches_ref_impl() {
    fn prop<Ty>(g: Graph<(), (), Ty>) -> bool
        where Ty: EdgeType
    {
        if g.edge_count() <= 500 && g.node_count() <= 500 {

            let cliques = maximal_cliques(&g);
            let cliques_ref = maximal_cliques_ref(&g);

            assert!(cliques.len() == cliques_ref.len());
            
            for c in &cliques_ref {
                assert!(cliques.contains(&c));
            }
        }
        true
    }
    quickcheck::quickcheck(prop as fn(Graph<_, _, Undirected>) -> bool);
    quickcheck::quickcheck(prop as fn(Graph<_, _, Directed>) -> bool);
}
