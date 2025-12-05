From Coq Require Import Setoid CMorphisms Relation_Definitions.
From HB Require Import structures.
Set Warnings "-notation-overridden, -notation-incompatible-prefix".
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ColorFun.

(* An edge coloring function assigns edges in E(G) to colors *)
Definition edge_coloring (G : sgraph) (ColorType : finType) : Type := {set G} -> ColorType.

(* A proper edge coloring is an edge coloring 
  where no two adjacent edges have the same color *)
Definition is_proper_edge_coloring {G : sgraph}
                                   {ColorType : finType} 
                                   (coloring : edge_coloring G ColorType) : Prop := 
  forall (e1 e2 : {set G}) (x:G), 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> x \in e1 -> x \in e2 -> coloring e1 != coloring e2.

Definition proper_edge_coloring (G : sgraph) (ColorType : finType) : Type :=
  { c : edge_coloring G ColorType | is_proper_edge_coloring c }.

(* the image under a coloring c of the set of edges E *)
Definition coloring_image {G : sgraph}
                          {ColorType : finType}
                          (E : {set {set G}})
                          (c : proper_edge_coloring G ColorType) : {set ColorType} := 
  [set sval c e | e in E].
Notation "c [ E ]" := (coloring_image E c) (at level 50).

(* A k-edge-coloring is a proper coloring which uses at most k colors *)
Definition k_edge_coloring (G : sgraph) (ColorType : finType) (k : nat) : Type := 
  { c : proper_edge_coloring G ColorType | #|c[E(G)]| = k }.

(* G is k-colorable if a k-edge-coloring exists *)
Definition k_edge_colorable (G : sgraph) (ColorType : finType) (k : nat) : Prop := 
  inhabited (k_edge_coloring G ColorType k).

(* The chromatic index chi is the smallest k such that G is k-colorable *)
Definition is_chromatic_index (G : sgraph) (chi : nat) : Prop :=
  k_edge_colorable G 'I_chi chi /\ forall k, k < chi -> ~ k_edge_colorable G 'I_k k.

(* injective coloring: each edge is a color *)
Definition inj_edge_coloring {G : sgraph} : edge_coloring G {set G} :=
  fun e => e.

Definition proper_inj_coloring {G : sgraph} : proper_edge_coloring G {set G}.
Proof.
  exists inj_edge_coloring => e1 e2 x _ _ _ _ _ //.
Defined.

Lemma inj_image (G : sgraph) : proper_inj_coloring[E(G)] = E(G). 
Proof.
  rewrite /coloring_image.
  apply/setP => e.
  apply/imsetP/idP. (* imsetP: prop->bool for set, idP: split into both directions *)
  - move=> [e' He' ->].
    rewrite /proper_inj_coloring /inj_edge_coloring /=.
    by [].
  - move=> He.
    exists e => //.
Qed.