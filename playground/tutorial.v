Set Warnings "-notation-overridden, -notation-incompatible-prefix". (* to ignore warnings due to the import of ssreflect *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
// removes all the trivial subgoals that can be resolved by the SSReflect tactic done described in 6.2, i.e., it executes try done. 
/= simplifies the goal by performing partial evaluation, as per the Coq tactic simpl. 
//= combines both kinds of simpli cation; it is equivalent to /= //, i.e., simpl; try done.
*)

Section HilbertSaxiom.

Variables A B C : Prop.
Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
    (*  => puts conclusions in context
        : is the inverse
        note, move does not actually do any of the work here
    *)
    move=> hAiBiC hAiB hA.
    apply: hAiBiC.
    (*
        move: (hAiBiC) would move this to the conclusion 
        but not remove it from the context
    *)
    - by [].
    - by apply: hAiB. (* shorthand for move=> hAiB. apply. *)
Qed.

Lemma HilbertS2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
    move=> hAiBiC hAiB hA.
    (* first tells us to do something in first subgoal generated *)
    apply: hAiBiC; first by apply: hA.
    exact: hAiB.
Qed.

Lemma HilbertS3 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
    move=> hAiBiC hAiB hA.
    (* hAiBiC has type A -> B -> C, and similar for the other two
        so (hAiBiC hA) has type B -> C *)
    by apply: hAiBiC (hAiB hA).
    (*
    rocq can infer and uses 'by' to solve trivially
    so could also just write hAiBiC (hAiB _)
    also, could use 'exact' instead of 'by apply'
    *)
Qed.

Check HilbertS.

End HilbertSaxiom.

Section Symmetric_Conjunction_Disjunction.

(* && is a function expecting 2 args and computing the bool of these
so the lemma expanded is (A && B = true) -> (B && A = true) *) 
Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof.   
    (* case splits inductive types *)
    by do 2! case. 
    (* equivalently, by case; case *)
Qed.

Lemma or_sym : forall A B :
    Prop, A \/ B -> B \/ A.
Proof. 
    (* [ tactic 1 | tactic 2] applies tactics to the subgoals *)
    by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl]. 
Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof.
    (* Semicolons required - tells it to apply to all subgoals *)
    (* move/orP : AorB rewrites AorB with orP and then applies to goal *)
    (* move/lemma modifies top of proof stack, apply/lemma modifies entire goal *)
    case; case; by move=> AorB; apply/orP; move/orP : AorB. 
Qed.

End Symmetric_Conjunction_Disjunction.

Section Smullyan_drinker.

Variables (D : Type)(P : D -> Prop).
Hypothesis (d : D) (EM : forall A, A \/ ~A).
    
Lemma drinker : exists x, P x -> forall y, P y.
Proof.
    case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy].
    - by exists y.
    - exists d. move=> _ y. (* move=> _ y ignores the first part of the proof stack *) 
    case: (EM (P y)) => // notPy.
    by case: nonotPy; exists y.
Qed.

End Smullyan_drinker.

Section Equality.

Variable f : nat -> nat.
Variable f10 : f 1 = f 0.
Hypothesis f00 : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
    move=> k k0.
    by rewrite k0.
Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof. 
    (* shorthand for move=> k hyp; rewrite {} hyp. 
    good for when hyp only used once *)
    by move=> k ->. 
Qed.

Lemma ff10 : f (f 1) = 0.
Proof.
    (* can do multiple rewrites w/ one step *)
    by rewrite f10 f00.
Qed.

End Equality.

Section Using_Definition.

Variable U : Type.
Definition set := U -> Prop.
Definition subset (A B : set) := forall x, A x -> B x.
Definition transitive (T : Type) (R : T -> T -> Prop) :=
    forall x y z, R x y -> R y z -> R x z.

Lemma subset_trans : transitive subset.
Proof.
    (* rewrite /def is ssreflect version of unfold def
        move=> def would also unfold before putting it in context
    *)
    rewrite /transitive /subset => x y z subxy subyz t xt.
    by apply: subyz; apply: subxy.
Qed.

End Using_Definition.

(* S n can be written n.+1 in ssreflect*)

(*
'plus' is defined by recursion with a fix point
and {struct n} in its definition tells us that recursion is done on the first argument

Sometimes when simplifying a goal, simpl. may simplify unwanted parts too (such as the addition)
Solution is to use addn = nosimpl plus. The notation + referes to addn 
See the different effects of simpl on the two lemmas
*)
Lemma concrete_plus : plus 16 64 = 80.
Proof. simpl. by []. Qed.

Lemma concrete_plus_bis : 16 + 64 = 80.
Proof. simpl. by []. Qed.

(* auto tactic - slow, but short
attempts to prove with tactics in arith 
47 = depth of the search *)
Lemma concrete_big_le : le 16 64.
Proof. by auto 47 with arith. Qed.

Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
    by elim=> [| n IHn m]; [elim | rewrite -[n.+1 + m]/(n + m).+1 IHn; elim: m].
Qed.

