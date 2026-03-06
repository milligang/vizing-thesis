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

Lemma edge_neigh_edge {G : sgraph} (x y : G) (e : {set G}) : 
  e \in E{x} -> e \in E{y} -> x != y -> (e = [set x; y]) /\ x -- y.
Proof.
  move/imsetP=> [z1] Hn1 He1.
  move/imsetP=> [z2] Hn2 He2.
  rewrite He2 in He1.
  case: (iffLR (doubleton_eq_iff y z2 x z1) He1);
  move=> [Hxy Hz]; first by rewrite Hxy eqxx.
  by rewrite in_opn -Hxy in Hn1; rewrite Hz setUC in He2.
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

Definition pathp_edge {G : sgraph} (x u v : G) (s : seq G) : Prop :=
  exists i, (i < size s) && (nth x (x::s) i == u) && (nth x s i == v).

Definition Path_edge {G : sgraph} {x y : G} (p : Path x y) (u v : G) := pathp_edge x u v (tail p).

Section PathEdge.
  Variables (G : sgraph) (x y z u v : G) (p : Path x y).

  Lemma is_path_edge : Path_edge p u v -> u -- v.
  Proof.
    rewrite/Path_edge/pathp_edge=> [[i] /andP[/andP[Hs /eqP <-] /eqP <-]].
    move: (pathpW (valP p))=> /pathP Hp.
    exact: Hp x i Hs.
  Qed.

  Lemma not_path_edge :
    ~ u -- v -> ~ Path_edge p u v.
  Proof.
    apply/contra_not; exact: is_path_edge.
  Qed.

  Lemma vert_not_in_path :
    (u \notin p) || (v \notin p) -> ~ Path_edge p u v.
  Proof.
    case/orP=> [Hu | Hv] [i /andP[/andP[Hs Hnl] Hnr]];
    [have : u \in p | have : v \in p].
  Admitted.

  Lemma edgep_path_edge (xy : x -- y) :
    (Path_edge (edgep xy) u v) <-> ((x == u) && (y == v)).
  Proof.
    rewrite/Path_edge/pathp_edge /=;
    split=> [[i]| Heq]; by [case i | exists 0].
  Qed.

  Lemma cat_path_edge (q : Path y z) :
    Path_edge (pcat p q) u v <-> Path_edge p u v \/ Path_edge q u v.
  Proof.
    rewrite/Path_edge -[tail (pcat p q)]/((tail p) ++ (tail q)) /pathp_edge size_cat;
    split=> [[i] /andP[/andP[Hs +] +] |].
    - rewrite nth_cat (nth_cat x (x :: tail p) (tail q) i).
      case Hi: (i < size (tail p)).
      + have Hlt : size (tail p) < size (x :: tail p) by [].
        have -> := leq_ltn_trans (ltnW Hi) Hlt=> Hnl Hnr.
        left; exists i; by rewrite Hi Hnl Hnr.
      + move/negbT: Hi; rewrite -leqNgt -cat1s size_cat /= ltnS => Hi Hnl Hnr.
        right; exists (i - size (tail p)).
        rewrite -(ltn_subLR (size (tail q)) Hi) in Hs.
        rewrite Hs (set_nth_default x y Hs) {}Hnr /= andbT.
        rewrite leq_eqVlt in Hi; move/orP: Hi Hnl=> [/eqP Hi | Hi];
        [move/esym/eq_leq: (Hi) | move/ltn_geF: (Hi)]=> ->.
        - have/eqP H0 : (size (tail p) - size (tail p)) == 0 by rewrite subn_eq0.
          by rewrite -Hi -last_nth path_last /= H0 nth0 => /eqP <-.
        - rewrite -cat1s nth_cat -[_ < 1]/(_ == 0) subn1 subn_eq0 leqNgt Hi /=.
          have Hlt : (i - size (tail p) - 1) < size (tail q) by rewrite subn1; exact: (leq_ltn_trans (leq_pred (i - size (tail p))) Hs).
          by rewrite (set_nth_default x y Hlt) addnC subnDA.
    - case; move=> [i] /andP[/andP[Hi Hnl] Hnr].
      + exists i.
        admit.
      + exists (size (tail p) + i).
  Admitted.

End PathEdge.

Lemma idp_path_edge {G : sgraph} (x u v : G) : Path_edge (idp x) u v -> False.
Proof.
  by rewrite/Path_edge/pathp_edge /= => [[_]].
Qed.
      





