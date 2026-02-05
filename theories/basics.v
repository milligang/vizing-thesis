Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_boot.
From Stdlib Require Import RelationClasses.
From GraphTheory Require Import digraph sgraph dom.
Require Import Stdlib.Logic.Classical_Prop.

Set Bullet Behavior "Strict Subproofs".

Lemma bipSubCom (n : nat) : subgraph ('K_n,1) ('K_n.+1).
Proof. 
    apply: sub_Kn.
    rewrite card_sum !card_ord. 
    by rewrite addn1.
Qed.

(* any singleton dominates K_n *)
Lemma domK n (v : 'K_n) :
    dominating [set v].
Proof.
    apply/forallP => u.
    rewrite /closed_neigh_set big_set1 /closed_neigh in_setU1 /orb.
    case: (u == v) /eqP => //.
    - move/eqP. rewrite in_opn. rewrite /edge_rel/=. by rewrite eq_sym.
Qed.
    