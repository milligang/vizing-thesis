From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section KempeGraph.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType).

  Definition kempe_pred := [pred e : {set G} | (c e == ca) || (c e == cb)].

  Definition kempeGraphType : sgraph := erestrict kempe_pred.
  
  Lemma kempe_edgeE (x y : G) :
    @edge_rel kempeGraphType x y =
    ((c [set x; y] == ca) || (c [set x; y] == cb)) && (x -- y).
  Proof. by []. Qed.

End KempeGraph.