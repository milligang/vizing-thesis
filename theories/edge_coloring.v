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
                                   (c : edge_coloring G ColorType) : Prop := 
  forall (e1 e2 : {set G}), 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> 
  (exists x, x \in e1 /\ x \in e2) -> c e1 != c e2.

Definition proper_edge_coloring (G : sgraph) (ColorType : finType) : Type :=
  { c : edge_coloring G ColorType | is_proper_edge_coloring c }.

Coercion proper_to_edge_coloring {G : sgraph} {ColorType : finType} 
  (pc : proper_edge_coloring G ColorType) : edge_coloring G ColorType :=
  proj1_sig pc.

(* the image under a coloring c of the set of edges E *)
Definition coloring_image {G : sgraph}
                          {ColorType : finType}
                          (E : {set {set G}})
                          (c : edge_coloring G ColorType) : {set ColorType} := 
  c @: E.
Notation "c [ E ]" := (coloring_image E c) (at level 50).

Lemma max_colors_at_vertex {G : sgraph} 
                     {ColorType : finType} 
                     (v : G)
                     (c : edge_coloring G ColorType) :
  #|c[E{v}]| <= max_degree G.
Proof.
  apply: (leq_trans (leq_imset_card _ _)).
  rewrite card_edge_neigh.
  rewrite /max_degree.
  exact: leq_bigmax_cond.
Qed.

(* ---- Chromatic Index ---- *)
(* A k-edge-coloring is a proper coloring which uses exactly k colors *)
Definition k_edge_coloring (G : sgraph) (k : nat) : Type := 
  { ColorType : finType &
    { c : proper_edge_coloring G ColorType | #|c[E(G)]| == k } }.

Coercion k_to_proper_coloring {G : sgraph} {k : nat} 
  (kc : k_edge_coloring G k) : 
  proper_edge_coloring G (projT1 kc) :=
  proj1_sig (projT2 kc).

Definition k_edge_card {G : sgraph} {k : nat } (c : k_edge_coloring G k) :
  #|c[E(G)]| == k :=
  proj2_sig (projT2 c).

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
  setD (c[E(G)]) (c[E{v}]).

Proposition exists_absent_color (G : sgraph) :
  k_edge_colorable G (max_degree G + 1) ->
  exists c : k_edge_coloring G (max_degree G + 1),
  forall v : G, absent_set v c != set0.
Proof.
  move=> [c]; exists c => v.
  rewrite -card_gt0 cardsDS; last by apply imsetS; apply sub_all_edges.
  by rewrite subn_gt0 
            (eqP (k_edge_card c)) 
            (leq_ltn_trans (max_colors_at_vertex v c)) 
            // addn1 ltnSn.
Qed.