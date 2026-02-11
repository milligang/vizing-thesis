From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries sgraph digraph.

Lemma bigmax_eq_pointwise (I :finType) (P : pred I) (F G: I -> nat) :
    {in P, forall x, F x = G x} -> \max_(i | P i) F i = \max_(i | P i) G i.
Proof.
  move => ?. elim/big_ind2 : _ => // y1 y2 x1 x2 A B.
  by rewrite A B.
Qed.

Lemma notin_setD {T : finType} (A B : {set T}) (x : T) :
  x \in A -> x \notin A :\: B -> x \in B.
Proof.
  rewrite in_setD => ->.
  by rewrite andbT negbK.
Qed.

Definition edge_neigh (G : sgraph) x := [set [set x; y] | y in N(G;x)].

Notation "E{ x }" := (@edge_neigh _ x) (at level 0, format "E{ x }").
Notation "E{ G ; x }" := (@edge_neigh G x) (at level 0, format "E{ G ; x }"). 

Lemma sub_all_edges {G : sgraph} (v : G) : E{v} \subset E(G).
Proof.
    apply/subsetP => e.
    rewrite/edge_neigh.
    move/imsetP => [w Hw ->].
    apply/edgesP; exists v, w.
    split => //.
    by rewrite in_opn in Hw.
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

Lemma del_edges1_neq {G : sgraph} (e del_e : {set G}) :
  e \in E(del_edges del_e) -> e != del_e.
Proof.
  move=> He.
  apply/eqP => Heq.
  rewrite Heq in He.
  by move: (del_edgesN del_e); rewrite He.
Qed.

Lemma card_edge_neigh (G : sgraph) (v : G) :
  #|E{v}| = #|N(v)|.
Proof.
    rewrite /edge_neigh.
    apply: card_imset => w1 w2.
    by rewrite doubleton_eq_left. 
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

  