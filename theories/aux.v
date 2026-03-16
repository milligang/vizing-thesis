From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma notin_setD {T : finType} (A B : {set T}) (x : T) :
  x \in A -> x \notin A :\: B -> x \in B.
Proof.
  rewrite in_setD => ->.
  by rewrite andbT negbK.
Qed.

Section preliminaries.
  Variables (T : finType).
  Implicit Types (A B : pred {set T}) (e : rel T).

  Lemma bigmax_eq_pointwise (P : pred T) (F G : T -> nat) :
    {in P, forall x, F x = G x} -> \max_(i | P i) F i = \max_(i | P i) G i.
  Proof.
    move => ?. by elim/big_ind2 : _ => // y1 y2 x1 x2 -> ->.
  Qed.

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
  Proof. move => irr_e x /=; by rewrite irr_e. Qed.

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

Section EdgeNeighboorhood.
  Definition edge_neigh (G : sgraph) x := [set [set x; y] | y in N(G;x)].

  Local Notation "E{ x }" := (@edge_neigh _ x) (at level 0, format "E{ x }").
  Local Notation "E{ G ; x }" := (@edge_neigh G x) (at level 0, format "E{ G ; x }"). 

  Lemma sub_all_edges {G : sgraph} (v : G) : E{v} \subset E(G).
  Proof.
      apply/subsetP => e.
      rewrite/edge_neigh.
      move/imsetP => [w Hw ->].
      apply/edgesP; exists v, w.
      split => //.
      by rewrite in_opn in Hw.
  Qed.

  Lemma edge_neigh_self {G : sgraph} {x y : G} (xy : x -- y) : [set x; y] \in E{x}.
  Proof.
    rewrite /edge_neigh; apply/imsetP; exists y;
    by rewrite -in_opn in xy.
  Qed.

  Lemma edge_neigh_edge {G : sgraph} (x y : G) (e : {set G}) : 
    ((e \in E{x}) && (e \in E{y}) && (x != y)) <-> (e == [set x; y]) && x -- y.
  Proof.
    split=> [/andP[/andP[/imsetP[z1] Hn1 He1 /imsetP[z2] Hn2 He2]]| /andP[/eqP Heq xy]].
    - rewrite He2 in He1.
      case: (iffLR (doubleton_eq_iff y z2 x z1) He1);
      move=> [Hxy Hz]; first by rewrite Hxy eqxx.
      rewrite in_opn -Hxy in Hn1; rewrite Hz setUC in He2.
      by move/eqP: He2.
    - move: (xy)=> /sg_edgeNeq ->.
      rewrite Heq (edge_neigh_self xy).
      have -> : [set x; y] = [set y; x] by apply/doubleton_eq_iff; right.
      by rewrite sg_sym in xy; rewrite (edge_neigh_self xy).
  Qed.

  Lemma del_edges_edge_neigh (G : sgraph) (A e : {set G}) (x : G) : 
    e \in E{del_edges A;x} = (e \in E{G;x}) && ~~ (e \subset A).
  Proof.
    rewrite/edge_neigh.
    apply/imsetP/andP => [[z + ->] | [/imsetP [z] Hin -> Hns]].
    - rewrite (del_edges_opn _ x) => /andP[Hin ->].
      by split; first apply/imsetP; try exists z.
    - move/andP: (conj Hin Hns). rewrite -del_edges_opn.
      by exists z.
  Qed.

  Lemma card_edge_neigh (G : sgraph) (v : G) :
    #|E{v}| = #|N(v)|.
  Proof.
      rewrite /edge_neigh.
      apply: card_imset => w1 w2.
      by rewrite doubleton_eq_left. 
  Qed.

End EdgeNeighboorhood.
Notation "E{ x }" := (@edge_neigh _ x) (at level 0, format "E{ x }").
Notation "E{ G ; x }" := (@edge_neigh G x) (at level 0, format "E{ G ; x }"). 

Lemma del_edges1_neq {G : sgraph} (e del_e : {set G}) :
  e \in E(del_edges del_e) -> e != del_e.
Proof.
  move=> He.
  apply/eqP => Heq.
  rewrite Heq in He.
  by move: (del_edgesN del_e); rewrite He.
Qed.

Definition max_degree (G : sgraph) : nat := \max_(x in G) #|N(x)|.

(* When we delete edges, it's easier to reason about E{x} *)
Lemma max_deg_edge (G : sgraph) : \max_(x in G) #|N(x)| = \max_(x in G) #|E{x}|.
Proof.
  apply: bigmax_eq_pointwise => v _; by rewrite card_edge_neigh.
Qed.

Lemma del_edges_max_deg (G : sgraph) (A : {set G} ):
  max_degree (del_edges A) <= max_degree G.
Proof.
  rewrite/max_degree 2!max_deg_edge.
  apply: bigmax_leq_pointwise => x _.
  apply: subset_leq_card.
  apply/subsetP => e.
  by rewrite (@del_edges_edge_neigh G A e) => /andP[-> _].
Qed.
      





