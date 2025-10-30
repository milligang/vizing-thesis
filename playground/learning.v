Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.
From Coq Require Import RelationClasses.
From GraphTheory Require Import edone preliminaries bij digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma divOr : forall (n m : nat), 
    2 %| n /\ 3 %| m -> 6 %| n * m.
Proof.
    move=> n m [/dvdnP [k A] /dvdnP [l B]].
    apply/dvdnP; exists (k * l).
    rewrite A B mulnACA. done. (* could use by, this is just to see it *)
Qed.

Check dvdnP.

Lemma sg_edgeNeq (G : sgraph) (x y : G) :
    x -- y -> (x == y = false).
Proof. 
    apply: contraTF => /eqP ->. 
    by rewrite sg_irrefl. 
Qed.

Lemma sg_edgeNeqExpanded (G : sgraph) (x y : G) :
    x -- y -> (x == y = false).
Proof.
    apply: contraTF. 
    move=> /eqP.
    move=> H.
    rewrite <- H.
    rewrite sg_irrefl.
    by [].
Qed.

(* Stack Exchange: https://stackoverflow.com/questions/31554453/why-are-logical-connectives-and-booleans-separate-in-coq/31568076#31568076
Excluded middle works for bools bc those are decidable
Lemma excluded_middle_bool :
  forall b : bool, b = true \/ negb b = true.
Proof. intros b; destruct b; simpl; auto. Qed.
*)
