From Coq Require Import Setoid CMorphisms Relation_Definitions.
From HB Require Import structures.
Set Warnings "-notation-overridden, -notation-incompatible-prefix".
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Definition *)
Section ColorEdgeSet.

(* Edge sets already defined, here we use simple graphs but could also do directed graphs (digraphs) *)  
Notation "E( G )" := (sg_edge_set G) (at level 0, G at level 99, format "E( G )").

(* Defined in connectivity
M is a set of edges, each edge is a set of two vertices
Definition matching (G : sgraph) (M : {set {set G}}) := 
  {subset M <= E(G) } /\ 
  {in M&, forall (e1 e2 : {set G}) (x:G), x \in e1 -> x \in e2 -> e1 = e2}. 

Also have Lemma matching_of_dimatching (G : sgraph) (A : {set G}) M : 
  dimatching M -> @matching G (matching_of M). so matching on digraph gives us matching on sgraph
*)

(* parition edges into sets P, each set is a matching (i.e. edges don't share vertices)
D is the set of edges in the graph (an edge is just a set of two vertices) *)
(* Definition edge_coloring (G : sgraph) (P : {set {set {set G}}}) (D : {set {set G}}) :=
  partition P D /\ [forall (S | S \in P), matching S]. This won't type check, matching is a Prop *)

Definition edge_coloring (G : sgraph) (P : {set {set {set G}}}) (D : {set {set G}}) :=
  partition P D /\ {in P, forall S, matching S}.

Definition trivial_edge_coloring (G : sgraph) (A : {set {set G}}) := 
  [set [set e] | e in A].

Lemma matching1 (G : sgraph) (e : {set G}) : e \in E(G) -> matching [set e].
Proof. split; last by move=> ? ? /set1P -> /set1P ->. 
Admitted. (* by move=> ? x; rewrite inE => /eqP ->. Qed. *)

Lemma trivial_edeg_coloringP (G : sgraph) (A : {set {set G}}) :
  edge_coloring (trivial_edge_coloring A) A.
Proof.
  split; last move=> ? /imsetP[e eA ->]. Check matching. exact: stable1.
  suff -> : trivial_coloring A = preim_partitiosn id A by apply: preim_partitionP.
  have E x : x \in A -> [set x] = [set y in A | x == y].
    by move=> xA; apply/setP => y; rewrite !inE eq_sym andb_idl // => /eqP<-.
  by apply/setP => P; apply/imsetP/imsetP => -[x xA ->]; exists x => //; rewrite E.
Qed.
Arguments trivial_coloringP {G A}.

(* edge chromatic number = chromatic index *)
Definition chi_mem (G : sgraph) (A : mem_pred {G * G}) := 
  #|[arg min_(P < trivial_edge_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

End ColorEdgeSet.


(* Functional Definition *)
Section ColorFun.

Variable (G : diGraph). (* Using digraph because simplegraph < digraph, so broader than sgraph *)
Variable Color : finType.

(* edge coloring function <-> assigns a color to exactly the edges in G *)
Definition edge_color_fun (color_fun : G -> G -> option Color) :=
  forall x y : G,
  if x -- y then exists c, color_fun x y == Some c
  else color_fun x y == None.

(* Valid edge coloring if no adjacent edges have the same color *)
Definition valid_edge_coloring (color_fun : G -> G -> option Color) :=
  (edge_color_fun color_fun) /\  
  (forall x y z : G, x -- y -> x -- z -> 
  (y == z) || (color_fun x y != color_fun x z)).

(* set of colors used to color edges of G connected to vertices V *)
Definition color_set (color_fun : G -> G -> option Color) (V : {set G}) : {set Color} :=
  \bigcup_(x in V) \bigcup_(y in V) 
    match color_fun x y with 
    | Some c => [set c]
    | None => set0
    end.

Definition edge_chromatic_num (H : diGraph) := 
  \min_(color_fun (* What to put here? *) : valid_edge_coloring color_fun) 
  #|color_set color_fun [set: H]|.
(*its either [set: H] or {set H}, essentially the same *)
End ColorFun.

(*
Potential implementations: 
- define a new type csgraph, a simple graph with a coloring relation
- similar to how sgraph < digraph, have csgraph < sgraph
- cedge : rel svertex
- need to require cedge <-> sedge
- given edge v-w, if exists u neq to w s.t. v-w and v-u, then v-w and v-u 
 must have diff colors
- so R x y != R x z
- I.E. R(x, _) is injective
- Need to enforce color <-> edge
    
Variable Color : finType.
Record cgraph := CGraph {
    cvertex : finType ; 
    cedge: rel cvertex; 
    color: cvertex -> cvertex -> Color; 
    cg_sym': symmetric cedge;
    cg_irrefl': irreflexive cedge; 
    color_inj': forall x, injective (color x);
    color_sym': forall x y, color x y = color y x
}.

Canonical sgraph_of (G : cgraph) := SGraph (@cg_sym' G) (@cg_irrefl' G).
Coercion sgraph_of : cgraph >-> sgraph.

How to define coloring? We want to count the colors used, so could define the set of colors used
This is the set of colors used to cover every edge in the graph
I.E. The number of Colors outputted by the color relation, for all v, w in graph s.t. cedge v w = true 

Also, could add option to pass in subgraph of G, could be useful later
currently using enum (cvertex G) but perhaps just pass in S : {set cvertex G}


Definition edge_colors (G : cgraph) : {set Color} := 
    [set color u v | u in enum (cvertex G), v in enum (cvertex G) & u -- v].
Definition n_colors (G : cgraph) : nat := #|edge_colors G|.

End CGraphDef.
*)
(*
----------
- could be nice to add this as a property, not a whole new graph type
- a map, takes in two vertices and returns color
- edge colorable if f x y != f x z forall x, y, z s.t. y != z
----------
- weird way: have a coloring, but assign two colors to every vertex
- require that at least one color must be shared between two vertices if edge relation
- and every vertex must have two distinct colors on it
---------
Vertex coloring defined as:
Definition coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :=
  partition P D && [forall S in P, stable S].
- the disjoint union of P covers D, and no vertices in S are adjacent for each S in P
- D is the vertices we are coloring, P is the sets of vertices for each color
-------- 
*)