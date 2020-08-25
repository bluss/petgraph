#![feature(test)]

extern crate petgraph;
extern crate rand;
extern crate test;


use rand::{Rng, thread_rng};

use petgraph::{Graph, Directed};
use petgraph::algo::{maximal_cliques};


#[bench]
fn bench_maximal_cliques(b: &mut test::Bencher) {
    let g = mk_directed_graph(100);
    b.iter(|| { maximal_cliques(&g)});
}

fn mk_directed_graph(nodes: usize) -> Graph<(), (), Directed> {
    let mut rng = thread_rng();
    let edge_prob = rng.gen_range(0., 1.) * rng.gen_range(0., 1.);
    let edges = ((nodes as f64).powi(2) * edge_prob) as usize;
    let mut gr = Graph::with_capacity(nodes, edges);
    for _ in 0..nodes {
        gr.add_node(());
    }
    for i in gr.node_indices() {
        for j in gr.node_indices() {
            if rng.next_f64() <= edge_prob {
                gr.add_edge(i, j, ());
            }
        }
    }
    gr
}
