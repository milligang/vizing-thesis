From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Setoid CMorphisms Relation_Definitions.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.
Require Import aux.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ---- Edge Coloring Functional Definition ---- *)
(* An edge coloring function assigns edges in E(G) to colors *)
Definition edge_coloring (G : sgraph) (ColorType : finType) : Type := {set G} -> ColorType.

(* A proper edge coloring is an edge coloring 
  where no two adjacent edges have the same color *)
(* Could do x in e1 instead *)
Definition is_proper_edge_coloring {G : sgraph}
                                   {ColorType : finType} 
                                   (coloring : edge_coloring G ColorType) : Prop := 
  forall (e1 e2 : {set G}), 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> 
  (exists x, x \in e1 /\ x \in e2) -> coloring e1 != coloring e2.

Definition proper_edge_coloring (G : sgraph) (ColorType : finType) : Type :=
  { c : edge_coloring G ColorType | is_proper_edge_coloring c }.

(* the image under a coloring c of the set of edges E *)
Definition coloring_image {G : sgraph}
                          {ColorType : finType}
                          (E : {set {set G}})
                          (c : proper_edge_coloring G ColorType) : {set ColorType} := 
  [set (sval c) e | e in E].
Notation "c [ E ]" := (coloring_image E c) (at level 50).

(* ---- Chromatic Index ---- *)
(* A k-edge-coloring is a proper coloring which uses at most k colors *)
Definition k_edge_coloring (G : sgraph) (k : nat) : Type := 
  { ColorType : finType &
    { c : proper_edge_coloring G ColorType | #|c[E(G)]| <= k } }.

(* G is k-colorable if a k-edge-coloring exists. *)
Definition k_edge_colorable (G : sgraph) (k : nat) : Prop := 
  inhabited (k_edge_coloring G k).

(* The chromatic index chi is the smallest k such that G is k-colorable *)
Definition is_chromatic_index (G : sgraph) (chi : nat) : Prop :=
  k_edge_colorable G chi /\ forall k, k < chi -> ~ k_edge_colorable G k.

(*  Any valid k-edge-colorable upper bounds chi *)
Lemma chromatic_index_upper_bound (G : sgraph) (chi k : nat) :
  is_chromatic_index G chi ->
  k_edge_colorable G k ->
  chi <= k.
Proof.
  move=> [Hchi_color Hchi_min] Hk.
  rewrite leqNgt.
  apply/negP => Hlt.
  have Hneg : ~ k_edge_colorable G k := Hchi_min _ Hlt.
  exact: Hneg Hk.
Qed.

(* ----  One-to-one Coloring ---- *)
(* injective coloring: each edge is a color *)
Definition inj_edge_coloring {G : sgraph} : edge_coloring G {set G} :=
  fun e => e.

(* injective coloring is a proper coloring *)
Definition proper_inj_coloring {G : sgraph} : proper_edge_coloring G {set G}.
Proof.
  exists inj_edge_coloring.
  move=> e1 e2 _ _ ne _.
  exact ne.
Defined.

Lemma inj_image {G : sgraph} : proper_inj_coloring[E(G)] = E(G). 
Proof.
  rewrite /coloring_image.
  apply/setP => e.
  apply/imsetP/idP.
  - move=> [e' He' ->].
    rewrite /proper_inj_coloring /inj_edge_coloring /=.
    by [].
  - move=> He.
    exists e => //.
Qed.

(* injective coloring is a k-edge-coloring with k = #|E(G)| *)
Definition inj_k_coloring {G : sgraph} : k_edge_coloring G #|E(G)|.
Proof.
  exists {set G}, proper_inj_coloring. by rewrite inj_image.
Defined.

(* Thus, all graphs have a k-edge-coloring with k = #|E(G)|*)
Lemma inj_chrom (G : sgraph) :
  k_edge_colorable G #|E(G)|.
Proof.
  constructor. exact inj_k_coloring.
Qed.

(* If chi is a chromatic index of G, then chi <= |E(G)| *)
Corollary chromatic_index_le_edges (G : sgraph) (chi : nat) :
  is_chromatic_index G chi -> chi <= #|E(G)|.
Proof.
  move=> Hchi. 
  apply (chromatic_index_upper_bound Hchi (inj_chrom G)).
Qed.

(* Absent Set *)
Definition absent_set {G : sgraph} {ColorType: finType} 
  (v : G) (c : proper_edge_coloring G ColorType) :=
  [set col in c[E(G)] | col \notin c[E{v}]].


