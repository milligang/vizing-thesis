From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries sgraph digraph.

Definition edge_neigh {G : sgraph} (u : G) := [set [set u; v] | v in N(u)].
Notation "E{ x }" := (edge_neigh x) (at level 0, format "E{ x }").

Lemma sub_all_edges {G : sgraph} (v : G) : E{v} \subset E(G).
Proof.
    apply/subsetP => e.
    rewrite /edge_neigh.
    move/imsetP => [w Hw ->].
    apply/edgesP; exists v, w.
    split => //.
    by rewrite in_opn in Hw.
Qed.

Lemma card_edge_neigh (G : sgraph) (v : G) :
  #|E{v}| = #|N(v)|.
Proof.
    rewrite /edge_neigh.
    apply: card_imset => w1 w2.
    by rewrite doubleton_eq_left. 
Qed.

Definition max_degree (G : sgraph) : nat := \max_(x in G) #|N(x)|.