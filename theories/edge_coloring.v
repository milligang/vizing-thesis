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

Lemma inj_im {G : sgraph} : proper_inj_coloring[E(G)] = E(G). 
Proof.
  apply/setP => e.
  apply/imsetP/idP.
  - move=> [e' He' ->].
    by rewrite /proper_inj_coloring /inj_edge_coloring /=.
  - move=> He.
    exists e => //.
Qed.

(* injective coloring is a k-edge-coloring with k = #|E(G)| *)
Definition inj_k_coloring {G : sgraph} : k_edge_coloring G #|E(G)|.
Proof.
  exists {set G}, proper_inj_coloring. by rewrite inj_im.
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

(* ----  Absent Set ---- *)
Definition absent_set {G : sgraph} {ColorType: finType} 
  (v : G) (c : edge_coloring G ColorType) :=
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

(* ---- Fans ---- *)
Section Fan.
Variable (G : sgraph) (ColorType : finType).
Implicit Types (v w : G) (e : {set G}) (f : seq G) (c : edge_coloring G ColorType).

(* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
Definition fan_prop_neigh v f := all (fun w => w \in N(v)) f.

(* 2. if w0 is the first item in fan f centered at v under coloring c,
  (v, w0) is a distinct color from the rest of the edges in the graph *)
Definition fan_prop_w0 e c := 
  [forall (h : {set G} | (h \in E(G)) && (e != h)), c e != c h].

(* 3. for all w_i, w_{i+1} in the fan f centered at v under coloring c,
  the color of (v, w_{i+1} is absent at w_i) *)
Definition fan_prop_absent e w c := 
  (c e) \in (absent_set w c).

Definition fan v wk c f := 
  uniq (wk::f) && 
  fan_prop_neigh v (wk::f) &&
  fan_prop_w0 [set v; (last wk f)] c &&
  path (
    fun x2 x1 => fan_prop_absent [set v; x2] x1 c
  ) wk f.

(* Definition maximal_fan v c := *)


End Fan.

Section Pack.
Variables (G : sgraph) (ColorType : finType).
Implicit Types (v w : G) (c : edge_coloring G ColorType).

Section FanDef.
  Variables (v w : G) (c : edge_coloring G ColorType).

  Record Fan : predArgType := { fval : seq G; _ : fan v w c fval }.

  HB.instance Definition _ := [isSub for fval].
  HB.instance Definition _ := [Countable of Fan by <:].

End FanDef.
End Pack.

Definition recolor_edge
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (e0 : {set G})
  (c0 : ColorType)
  : edge_coloring G ColorType :=
  fun e => if e == e0 then c0 else c e.

Lemma recolor_eq
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType) e0 c0 :
  (recolor_edge c e0 c0) e0 = c0.
Proof. by rewrite /recolor_edge eqxx. Qed.

Lemma recolor_neq
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType) e0 e1 c0 :
  e1 != e0 ->
  (recolor_edge c e0 c0) e1 = c e1.
Proof. by rewrite /recolor_edge => /negPf ->. Qed.

Definition swap_edge
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (e0 e1 : {set G})
  : edge_coloring G ColorType :=
  fun e => 
    if e == e0 then c e1
    else if e == e1 then c e0
    else c e. 

Lemma swap_im
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (e0 e1 : {set G}) :
  e0 \in E(G) ->
  e1 \in E(G) ->
  c[E(G)] = (swap_edge c e0 e1)[E(G)].
Proof.
  move=> He0 He1; apply/setP => col.
  apply/imsetP/imsetP; move=> [e2 He2 ->];
  exists (if e2 == e0 then e1 else if e2 == e1 then e0 else e2) => //;
  rewrite /swap_edge;
  case: ifP => [/eqP He | Hne] //.
  admit.
  (* case: ifP => H.
  - exists e1=> //.
   [/eqP -> | Hne0].
Qed. *)

  (* apply/imsetP/imsetP; move=> [e He ->]; 
  exists e => //.
  rewrite /swap_edge; case: ifP. *)
Admitted.

Fixpoint rotate_seq
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (v : G)
  (f : seq G)
  (prev : G)
  : edge_coloring G ColorType :=
  match f with
  | [::] => c
  | w :: ws =>
    rotate_seq
        (swap_edge c [set v; prev] [set v; w])
        v ws w
  end.

Lemma rotate_seq_im
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (v prev : G) (f : seq G) :
  c @: E{v} =
  rotate_seq c v f prev @: E{v}.
Proof.
  elim: f c prev => [|w ws IH] c prev /=; first by reflexivity.
Admitted.
  (* rewrite -(swap_im c [set v; prev] [set v; w]).
  exact: IH.
Qed. *)

Section Rotation. 
Variables (G : sgraph) (ColorType : finType) (v wk : G) (c : edge_coloring G ColorType) (f : Fan v wk c).

Definition len : nat := size (val f) + 1.

Definition fan_nodes := locked (wk :: val f).

Definition rot : edge_coloring G ColorType := 
  let rev_fan := rev fan_nodes in
  rotate_seq c v rev_fan (head wk rev_fan).

Lemma rot_im :
  c @: E{v} = rot @: E{v}.
Proof.
  rewrite /rot.
  exact: rotate_seq_im.
Qed.

(* decide if want single element or set equality *)
Lemma rot_abs_edge (c0 : ColorType) :
  c0 \in absent_set v c ->
  c0 \in absent_set v rot.
Proof.
  rewrite/absent_set.
Admitted.

Lemma rot_single : 
  len == 1 -> 
  forall e, c e == rot e.
Proof.
Admitted.

Lemma rot_card :
  #|c @: E(G)| == #|rot @: E(G)|.
Proof. 
Admitted.

(* Needs to be fixed in latex, require premise c is proper *)
Lemma rot_proper : 
  is_proper_edge_coloring c ->
  is_proper_edge_coloring rot.
Proof. 
Admitted.

End Rotation.


 
