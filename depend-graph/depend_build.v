From dpdgraph Require dpdgraph.
From VizingThesis Require edge_coloring vizing.

Set DependGraph File "vizing-thesis/depend-graph/graph.dpd".

(* Print FileDependGraph edge_coloring. *)
(* Print FileDependGraph vizing. *)

(* 
    Step through to here, or make
    dpd2dot graph.dpd && python3 filter_dpd.py && xdot graph_filtered.dot
    see https://github.com/rocq-community/coq-dpdgraph?tab=readme-ov-file
*)