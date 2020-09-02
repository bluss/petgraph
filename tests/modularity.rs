use petgraph::algo::modularity;
use petgraph::prelude::*;
use petgraph::Graph;

#[test]
fn modularity_test() {
    let mut graph: UnGraph<(), ()> = Graph::new_undirected();
    let a = graph.add_node(());
    let b = graph.add_node(());
    let c = graph.add_node(());
    let d = graph.add_node(());
    let e = graph.add_node(());
    let f = graph.add_node(());
    let g = graph.add_node(());
    let h = graph.add_node(());
    let i = graph.add_node(());
    let j = graph.add_node(());
    let k = graph.add_node(());
    let l = graph.add_node(());
    let m = graph.add_node(());

    graph.extend_with_edges(&[
        (a, b),
        (b, c),
        (c, d),
        (b, f),
        (f, g),
        (c, g),
        (g, h),
        (d, e),
        (e, h),
        (h, i),
        (h, j),
        (h, k),
        (h, l),
        (i, m),
        (l, k),
        (j, k),
        (j, m),
        (k, m),
        (l, m),
        (m, e),
    ]);

    let res = modularity(&graph, |n| if n  == a || n == b || n == c { 1 } else {0});
    let expected_res = 0.1387500000000001;
    assert_eq!(res, expected_res);
}
