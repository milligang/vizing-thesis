# About

To date, we have found no public proof of Vizing's Theorem in Rocq. 
This is a key theorem for edge colorings in graphs; hence, the purpose of this repository is to provide a proof for Vizing's Theorem in Rocq, as an extension of the graph-theory library in MathComp, and to provide a common definition of edge-coloring that integrates with the existing graph-theory library.

## To Run
Clone the repository. In your terminal, run 'make -f CoqMakefile' to build.

## Files and folders 
- alternate_paath.v: Defines a kempe chain as an alternating path structure and kempe swap as a recursive function applied to the path; this is an alternative implementation of the material in kempe.v and most lemmas here are admitted
- aux.v: Often helpful material for the proof of Vizing's Theorem, though has independent applications, such as a set of edges adjacent to a vertex.
- basics.v: Lemmas and theorems proven over the course of the project, especially when we were familiazing ourselves with the library, which are not directly related to the proof of Vizing's Theorem
- depend-graph: builds a dependency graph for a file
- edge_coloring.v: Definition of edge-coloring in ssreflect
- fans.v: Defines a fan as a sequence of vertices centered at some vertex v satisfying the typical properties of a fan in edge-coloring graph theory, and includes a rotation operation of the fan
- kempe.v: Defines a kempe chain as a component of a subgraph of G in which all edges are one of two colors
- spath.v: Results about paths as defined in the graph theory library. Similar to aux.v, this material supports the proof of Vizing's Theorem but also has independent applications.
- vizing.v: Contains the proof of Vizing's Theorem. There are two complete proofs in this file. Theorem Vizings_altpath utilizes the material in alternate_path.v while Theorem Vizings_kempe utilizes the material in kempe.v.
  
## Requirements

The code in this repository requires the dependencies of package [_graph-theory 0.8_](https://github.com/coq-community/graph-theory):
Coq 8.11+, MathComp 1.10+, finmap, hierarchy builder 0.10.

In our case, we use Rocq version 9.1.0 compiled with OCaml 4.14.2. 
We also use the Equations pluggin for recursive functions. If you're using opam, this can be installed by running 'opam install rocq-equations'.

## Authors and contact information

- Milligan Grinstead ([**@milligang**](https://github.com/milligang))


