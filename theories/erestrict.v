From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section preliminaries.
  Variables (T : finType).
  Implicit Types (A B : pred {set T}) (e : rel T).

  Definition restrict2_mem (P : mem_pred {set T}) e := 
    [rel u v | in_mem [set u; v] P && e u v].
  Local Notation restrict2 P := (restrict2_mem (mem P)).

  Lemma sub_restrict2 A e :
    subrel (restrict2 A e) e.
  Proof. move => x y /=. by case: (e x y); case: (_ \in A). Qed.

  Lemma restrict2_mono A B e :
    {subset A <= B} -> subrel (restrict2 A e) (restrict2 B e).
  Proof. move => H x y /= => /andP [HA ->]. by rewrite !H. Qed.

  Lemma restrict2_irrefl A e : 
    irreflexive e -> irreflexive (restrict2 A e).
  Proof. move => irr_e x /=. by rewrite irr_e. Qed.

  Lemma restrict2_sym A e : 
    symmetric e -> symmetric (restrict2 A e).
  Proof. move => sym_e x y /=. by rewrite sym_e setUC. Qed.

  Lemma erpath_sub A e x p : 
    path (restrict2 A e) x p -> path e x p.
  Proof.
    elim: p x => //= b p IH x. rewrite -!andbA => /and3P[H1 H2 H3].
    by rewrite H2 (IH b H3).
  Qed.

  (* restrict in preliminaries is actually a special case of restrict2 *)
  Lemma restrict_eq_restrict2 (P : pred T) e :
    restrict P e =2 restrict2 [pred f : {set T} | f \subset P] e.
  Proof.
    move => x y /=; rewrite /restrict_mem /restrict2_mem inE.
    apply/andb_id2r => _. 
    apply/andP/subsetP=> [[+ +] z /set2P [-> //|-> //]| H].
    by split; [apply/H/set21 | apply/H/set22].
  Qed.

  Lemma restrict2E A e: 
    A =i predT -> connect (restrict2 A e) =2 connect e.
  Proof. 
    move => H x y. rewrite (eq_connect (e' := e)) //. 
    move => {x y} x y /=. by rewrite !H.
  Qed.

End preliminaries.
Notation restrict2 A := (restrict2_mem (mem A)).

Section erestrictGraph.
  Variables (G : sgraph) (A : pred {set G}).

  Lemma symmetric_restrict2_sedge :
    symmetric (restrict2 A (--)).
  Proof. apply: restrict2_sym. exact: sg_sym. Qed.

  Lemma erestrict_sym :
    connect_sym (restrict2 A (--)).
  Proof. exact/connect_symI/symmetric_restrict2_sedge. Qed.

  Lemma sedge_in_equiv2 :
    equivalence_rel (connect (restrict2 A (--))).
  Proof. exact/equivalence_rel_of_sym/symmetric_restrict2_sedge. Qed.

  Definition erestrict : sgraph :=
    Eval hnf in SGraph (restrict2_sym A (@sg_sym G))
                      (restrict2_irrefl A (@sg_irrefl G)).

  Lemma upathPR (x y : G) :
    reflect (exists p : seq G, @upath erestrict x y p)
            (connect (restrict2 A (--)) x y).
  Proof. exact: (@upathP erestrict). Qed.

  Lemma erestrict_sub : subgraph erestrict G.
  Proof. by exists id=> // u v /andP[_ ->]. Qed.
End erestrictGraph.

Section KempeGraph.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (ca cb : ColorType).

  Definition kempe_pred := [pred e : {set G} | (c e == ca) || (c e == cb)].

  Definition kempe_graph : sgraph := erestrict kempe_pred.
  
  Lemma kempe_edgeE (x y : G) :
    @edge_rel kempe_graph x y =
    ((c [set x; y] == ca) || (c [set x; y] == cb)) && (x -- y).
  Proof. by []. Qed.

End KempeGraph.