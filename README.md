# About

To date, we have found no public proof of Vizing's Theorem in Rocq or Lean. 
This is a key theorem for edge colorings in graphs; hence, the purpose of this repository is to provide a proof for Vizing's Theorem in Rocq, as an extension of the graph-theory Rocq library.

## Files and folders 
- basics.v: Lemmas and theorems proven over the course of the project, especially when we were familiazing ourselves with the library, which are not directly related to the proof of Vizing's Theorem
- aux.v: Structures helpful for the proof of Vizing's Theorem but not directly involved and have independent applications, such as a set of edges adjacent to a vertex.
- edge_coloring.v: Definition of edge-coloring in ssreflect
  
## Requirements

The code in this repository requires the dependencies of package [_graph-theory 0.8_](https://github.com/coq-community/graph-theory):
Coq 8.11+, MathComp 1.10+, finmap, hierarchy builder 0.10.

In our case, we use Rocq version 9.0.0 compiled with OCaml 4.14.2. 

## Authors and contact information

- Milligan Grinstead ([**@milligang**](https://github.com/milligang))

