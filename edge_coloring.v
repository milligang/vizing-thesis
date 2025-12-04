From Coq Require Import Setoid CMorphisms Relation_Definitions.
From HB Require Import structures.
Set Warnings "-notation-overridden, -notation-incompatible-prefix".
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ColorFun.
Variable (G : sgraph).

(* An edge coloring function assigns edges (sets of vertices) to colors *)
Definition edge_coloring (ColorSet : finType) := {set G} -> ColorSet.

(* A proper edge coloring is an edge coloring 
  where no two adjacent edges have the same color *)
Definition is_proper_edge_coloring (ColorSet : finType) (coloring : edge_coloring ColorSet) : Prop := 
  {in E(G)&, forall (e1 e2 : {set G}) (x:G), x \in e1 -> x \in e2 -> coloring e1 != coloring e2}.

Definition proper_edge_coloring (ColorSet : finType) := 
  {coloring : edge_coloring ColorSet | is_proper_edge_coloring coloring}.

(* A k-edge-coloring is a proper coloring which uses at most k colors *)
Definition k_edge_coloring (k : nat) := proper_edge_coloring 'I_k.

(* G is k-colorable if a k-edge-coloring exists *)
Definition k_colorable (k : nat) : Prop := 
  inhabited (k_edge_coloring k).

(* The chromatic index chi is the smallest k such that G is k-colorable *)
Definition is_chromatic_index (chi : nat) : Prop :=
  k_colorable chi /\ forall k, k < chi -> ~ k_colorable k.

(**** NOT CHECKED BELOW ****)
(** Extend a coloring when adding an edge *)
Definition extend_coloring (G : sgraph) (ColorSet : finType) 
  (chi : edge_coloring_fun G ColorSet) (x y : G) (c : ColorSet) 
  : edge_coloring_fun (add_edge x y) ColorSet :=
  fun e => if e == [set x; y] then c else chi e.

(** Switch two colors in a coloring *)
Definition switch_colors (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) (c1 c2 : Color)
  : edge_coloring_fun G Color :=
  fun e => if chi e == c1 then c2 
           else if chi e == c2 then c1 
           else chi e.

(** Switch colors only on a subset of edges *)
Definition switch_colors_on (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) (S : {set {set G}}) (c1 c2 : Color)
  : edge_coloring_fun G Color :=
  fun e => if e \in S then 
             (if chi e == c1 then c2 
              else if chi e == c2 then c1 
              else chi e)
           else chi e.

(** Recolor a specific edge *)
Definition recolor_edge (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) (e : {set G}) (c : Color)
  : edge_coloring_fun G Color :=
  fun e' => if e' == e then c else chi e'.

(** The set of colors used by a coloring *)
Definition colors_used (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) : {set Color} :=
  chi @: E(G).

(** The set of colors used at a vertex (colors of incident edges) *)
Definition colors_at_vertex (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) (v : G) : {set Color} :=
  [set chi e | e in E(G) & v \in e].

(** Find an available color at a vertex *)
Definition available_color (G : sgraph) (Color : finType)
  (chi : edge_coloring_fun G Color) (v : G) : option Color :=
  pick [pred c | c \notin colors_at_vertex chi v].

End ColorFun.
