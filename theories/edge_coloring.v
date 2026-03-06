From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EdgeColoring.
  (* ---- Edge Coloring Functional Definition ---- *)
  Variables (G : sgraph) (ColorType : finType).
  Implicit Type (x : G).

  (* An edge coloring function assigns edges in E(G) to colors *)
  Definition edge_coloring : Type := {set G} -> ColorType.
  Implicit Type (c : edge_coloring).
  
  Definition is_proper_edge_coloring c : Prop := 
    forall (x : G),
    {in E{x}&, forall (e1 e2 : {set G}), c e1 = c e2 -> e1 = e2}.

  Definition proper_edge_coloring : Type := { c | is_proper_edge_coloring c }.
  Implicit Type (pc : proper_edge_coloring).

  Coercion proper_to_edge_coloring
    pc : edge_coloring := proj1_sig pc.

  (* TO THINK: Should we remove this notation? It matches the write-up, but may just add confusion for the rocq code *)
  Definition coloring_image c (E : {set {set G}}) : {set ColorType} := c @: E.
  Local Notation "c [ E ]" := (coloring_image c E) (at level 50).

  Lemma c_in_edge_neigh c x (c0 : ColorType) : 
    reflect (exists2 y, [set x; y] \in E(G) & c [set x; y] = c0) (c0 \in c[E{x}]).
  Proof.
    rewrite/edge_neigh; apply/(iffP idP)=>[/imsetP[e] /imsetP[y]|[y] He Hc].
    - rewrite in_opn -in_edges=> Hin He Hc; rewrite He in Hc.
      by exists y.
    - apply/imsetP; exists [set x; y]=> //=.
      apply/imsetP; exists y; by rewrite // in_opn -in_edges He.
  Qed.
  
  Lemma c_in_all_edge c (c0 : ColorType) :
    reflect (exists2 e, e \in E(G) & c e = c0) (c0 \in c[E(G)]).
  Proof.
    apply/(iffP idP)=> [/imsetP[e] He /esym|[e] /edgesP [x] [y] [He Hxy]] Hc; first by exists e.
    rewrite -in_edges in Hxy; rewrite He in Hc.
    have : (c0 \in c[E{x}]) by apply/c_in_edge_neigh; exists y.
    rewrite -2!sub1set=> Hsub. 
    exact: (subset_trans Hsub (imsetS c (sub_all_edges x))).
  Qed.

  Lemma leq_col_deg c x : #|c[E{x}]| <= max_degree G.
  Proof. 
    apply: (leq_trans (leq_imset_card _ _)).
    rewrite card_edge_neigh.
    rewrite /max_degree.
    exact: leq_bigmax_cond.
  Qed.

  Lemma eq_deg_pcol pc x : #|pc[E{x}]| = #|E{x}|.
  Proof.
    apply: card_in_imset.
    exact: (proj2_sig pc). 
  Qed.

  Lemma leq_vertex_graph c x : #|c[E{x}]| <= #|c[E(G)]|.
  Proof.
    apply: subset_leq_card (imsetS c (sub_all_edges x)).
  Qed.

  Lemma leq_maxdeg_pcol pc : max_degree G <= #|pc[E(G)]|.
  Proof.
    rewrite /max_degree max_deg_edge.
    apply/bigmax_leqP=> x _. 
    apply: (leq_trans _ (leq_vertex_graph pc x)).
    by rewrite (eq_deg_pcol pc x).
  Qed.

End EdgeColoring.
Notation "c [ E ]" := (coloring_image c E) (at level 50).

Section ChromIdx.
  Variables (G : sgraph).
  Implicit Types (k chi : nat).
  
  (* A k-edge-coloring is a proper coloring which uses exactly k colors *)
  Definition k_edge_coloring k : Type := 
    { ColorType : finType &
      { c : proper_edge_coloring G ColorType | #|c[E(G)]| == k } }.

  Coercion k_to_proper_coloring {k} (kc : k_edge_coloring k) : 
    proper_edge_coloring G (projT1 kc) :=
    proj1_sig (projT2 kc).

  Definition proper_to_k_coloring 
    {ColorType : finType} (pc : proper_edge_coloring G ColorType) 
  : k_edge_coloring #|pc[E(G)]| := (existT _ ColorType (exist _ pc (eqxx _))).

  Definition card_k_col {k} (kc : k_edge_coloring k) :
    #|kc[E(G)]| = k := eqP (proj2_sig (projT2 kc)).

  (* G is k-colorable if a k-edge-coloring exists. *)
  Definition k_edge_colorable k : Prop := inhabited (k_edge_coloring k).

  (* The chromatic index chi is the smallest k such that G is k-colorable *)
  Definition is_chromatic_index chi : Prop :=
    k_edge_colorable chi /\ forall k, k < chi -> ~ k_edge_colorable k.

  (* We can already lower bound the chromatic index *)
  Theorem chi_lower_bound chi : 
    is_chromatic_index chi -> 
    max_degree G <= chi.
  Proof. 
    do 3![elim] => ColorType H _. 
    elim: H=> c /eqP <-.
    by rewrite leq_maxdeg_pcol.
  Qed.

  (* Any valid k-edge-coloring upper bounds chi *)
  Lemma chi_upper_bound k chi :
    is_chromatic_index chi ->
    k_edge_colorable k ->
    chi <= k.
  Proof.
    move=> [Hchi_color Hchi_min] Hk.
    rewrite leqNgt.
    apply/negP => Hlt.
    have Hneg : ~ k_edge_colorable k := Hchi_min _ Hlt.
    exact: Hneg Hk.
  Qed.

  Lemma chi_upper_bound_trans k chi :   
    is_chromatic_index chi ->
    (exists n, k_edge_colorable n /\ n <= k) ->
    chi <= k.
  Proof.
    move=> Hchi [n] [Hk Hltn].
    have Hltk : chi <= n by exact/chi_upper_bound.
    exact (leq_trans Hltk Hltn).
  Qed.

  (* ----  One-to-one Coloring ---- *)

  (* TO THINK: we could use Program Definition, is this better? Should we do this elsewhere too? *)
  (* Program Definition in_edge_coloring2 : proper_edge_coloring G {set G} := 
    fun e => e. *)

  (* injective coloring: each edge is a color *)
  Definition inj_edge_coloring : edge_coloring G {set G} :=
    fun e => e.

  Definition proper_inj_coloring : proper_edge_coloring G {set G}.
  Proof.
    exists inj_edge_coloring.
    by move=> _ e1 e2 _ _ eq.
  Defined.

  Lemma imset_inj : proper_inj_coloring[E(G)] = E(G). 
  Proof.
    apply/setP => e.
    apply/imsetP/idP.
    - move=> [e' He' ->].
      by rewrite /proper_inj_coloring /inj_edge_coloring /=.
    - move=> He.
      exists e => //.
  Qed.

  Definition inj_k_coloring : k_edge_coloring #|E(G)|.
  Proof.
    exists {set G}, proper_inj_coloring. by rewrite imset_inj.
  Defined.

  (* Thus, all graphs have a k-edge-coloring with k = #|E(G)|*)
  Lemma inj_chrom : k_edge_colorable #|E(G)|.
  Proof.
    constructor. exact inj_k_coloring.
  Qed.

  (* If chi is a chromatic index of G, then chi <= |E(G)| *)
  Corollary chromatic_index_le_edges chi :
    is_chromatic_index chi -> chi <= #|E(G)|.
  Proof.
    move=> Hchi. 
    apply (chi_upper_bound Hchi inj_chrom).
  Qed.

  (* TO THINK: could also prove chromatic index exists and is unique *)
End ChromIdx.

Section AbsentSet.
  Variables (G : sgraph).
  Implicit Types (x y : G).

  Definition absent_set {ColorType : finType} 
    (c : edge_coloring G ColorType) x :=
    setD (c[E(G)]) (c[E{x}]).

  (* still deciding on definitions further down, tbd which of these three will be needed *)
  (* Lemma absent_col {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x :
    c0 \in absent_set c x <-> [pick e in E{x} | c e == c0] == None.
  Proof. split=> H. Admitted. *)

  Lemma absent_edge {ColorType : finType} (c : edge_coloring G ColorType) (c0 : ColorType) x y :
    c0 \in absent_set c x -> y \in N(x) -> c0 != c [set x; y].
  Proof.
    move=> /setDP[_ /memPnC Hnin] Hn.
    have Hin : c [set x; y] \in c[E{x}].
    { by apply/imsetP; exists [set x; y]; first by apply/imsetP; exists y. }
    by apply Hnin.
  Qed.

  Proposition exists_absent_color {k : nat} (kc : k_edge_coloring G k):
    max_degree G + 1 <= k ->
    forall x : G, exists c, c \in (absent_set kc x).
  Proof.
    rewrite addn1=> Hk x; apply/set0Pn.
    rewrite -card_gt0 cardsDS; last by apply imsetS; apply sub_all_edges.
    by rewrite subn_gt0 (card_k_col kc) (leq_ltn_trans (leq_col_deg kc x)).
  Qed.
  
End AbsentSet.

Section ExtendCol. 
  Variables (G : sgraph) (del_e : {set G}) (He : del_e \in E(G)).

  Definition extended_col 
    {ColorType : finType}
    (c : edge_coloring (del_edges del_e) ColorType)
  : edge_coloring G (option ColorType) :=
    fun e => if e == del_e then None else Some (c e).

  Lemma proper_extended_col
    {ColorType : finType}
    (pc : proper_edge_coloring (del_edges del_e) ColorType)
  : is_proper_edge_coloring (extended_col pc).
  Proof.
    move:pc => [c Hp] x f0 f1 Hf0 Hf1.
    rewrite/extended_col.
    case H00: (f0 == del_e); case H10 : (f1 == del_e) => //.
    - move/eqP: H00 => ->; move/eqP: H10 => -> //.
    move=> [Heq]; apply (Hp x); last by [];
    move/negbT: H00=> H00; move/negbT: H10=> H10;
    move/(subsetP (sub_all_edges x)): (Hf0)=> Hf0G;
    move/(subsetP (sub_all_edges x)): (Hf1)=> Hf1G;
    move: (edges_eqn_sub Hf0G He H00)=> Hsub0;
    move: (edges_eqn_sub Hf1G He H10)=> Hsub1;
    by rewrite (@del_edges_edge_neigh G del_e _ _).
  Qed.

  (* TODO: Should be straightforward, need to figure out which tactic to use *)
  Lemma card_extended_col 
    {k : nat} 
    (kc : k_edge_coloring (del_edges del_e) k) 
  : #|extended_col kc[E(G)]| = k + 1.
  Proof. 
    rewrite/extended_col/coloring_image.
    rewrite (del_edges1 He).
    rewrite imsetU1 eq_refl.
    (* under eq_imset => e. rewrite (del_edges1_neq). *)
    (* rewrite del_edgesN. *)
    (* move: kc => [CT [pc Hcard]]. *)
    (* exists (option CT), (proper_extended_col pc). *)
  Admitted.

  (* extended_col of a k-edge-coloring produces a (k+1)-edge-coloring *)
  Definition k_extended_col 
    {k : nat}
    (kc : k_edge_coloring (del_edges del_e) k)
  : k_edge_coloring G (k + 1).
  Proof.
    exists (option (projT1 kc)), 
    (exist _ (extended_col kc) (@proper_extended_col _ kc));
    by rewrite (card_extended_col kc). 
  Defined.

  Lemma extended_absent 
    {k : nat}
    {kc : k_edge_coloring (del_edges del_e) k}
    {c0 : projT1 kc}
    {x : G}
    (H : c0 \in absent_set kc x)
  : Some c0 \in absent_set (k_extended_col kc) x.
  Proof.
  Admitted.
  
End ExtendCol.

Section Recolor.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (e f : {set G}).

  Definition recolor_edge e c0 : edge_coloring G ColorType :=
    fun edge => if edge == e then c0 else c edge.

  Lemma recolor_eq e c0 : (recolor_edge e c0) e = c0.
  Proof. by rewrite /recolor_edge eqxx. Qed.

  Lemma recolor_neq e f c0 : f != e -> (recolor_edge e c0) f = c f.
  Proof. by rewrite /recolor_edge=> /negPf ->. Qed.

  Lemma del_edges_imset_recolor e c0 : 
    c[E(del_edges e)] = recolor_edge e c0 [E(del_edges e)].
  Proof.
    apply/setP => c1.
    by apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /recolor_edge;
    exists e2 => //; case: ifP => /eqP Heq //;
    rewrite Heq in He2; move: (del_edgesN e); rewrite -in_setC => /setCP.
  Qed.

  Lemma imset_recolor e c0 :
    c0 \in c[E(G)] ->
    recolor_edge e c0 [E(G)] \subset c[E(G)].
  Proof.
  Admitted.

  (* TO DO: will likely make a lemma related to absent set, since we will use similar logic for swap_proper_vertex
    but this specifically is needed for the smaller lemma at the end, 
    mostly just LOTS of case work now though reasonably straightforward
    some of the cases are relatively similar
  *)
  Lemma recolor_proper (x y : G) c0 :
    is_proper_edge_coloring c ->
    c0 \in (absent_set c x :&: absent_set c y) ->
    is_proper_edge_coloring (recolor_edge [set x; y] c0).
  Proof.
    rewrite/recolor_edge in_setI=> Hp /andP[Hax Hay].
    move: Hp=> Hp z e1 e2.
    case: (x =P y)=> [-> |/eqP Hxy].
    - case: ifP=> [/eqP -> |_ He1]; 
      case: ifP=> [/eqP ->|_];
      try (by move: He1; exact: (Hp z));
      by move=> H; have := subsetP (sub_all_edges z) _ H;
      rewrite in_edges sg_irrefl.
    case Hx1: (e1 \in E{x}); case Hy1: (e1 \in E{y});
    case Hx2: (e2 \in E{x}); case Hy2: (e2 \in E{y}).
    have [-> A2]:= edge_neigh_edge _ _ _ Hx1 Hy1 Hxy.
    rewrite eq_refl.
  (*     
    case Heq2: (e2 == [set x; y]).
    - move/eqP: Heq1 => ->; move/eqP: Heq2 => -> //.
    move: (Hp _ _ _ He1 He2). *)
  Admitted.


  Lemma replace_col e c0 : 
    e \in E(G) ->  
    c0 \in c[E(del_edges e)] ->
    c e \notin c[E(del_edges e)] -> 
    #|recolor_edge e c0 [E(G)]| = #|c[E(G)]| - 1.
  Proof.
    move=> He.
    rewrite (del_edges1 He).
    move: (del_edges_imset_recolor e c0).
    rewrite /coloring_image 2!imsetU1 2!cardsU1 recolor_eq => -> -> -> /=.
    by rewrite add0n add1n subn1.
  Qed.

  Definition swap_edge e f : edge_coloring G ColorType :=
    fun edge => 
      if edge == e then c f
      else if edge == f then c e
      else c edge. 
  
  Lemma swap_edge_eq {e f} : e == f -> swap_edge e f =1 c.
  Proof.
    move=> /eqP -> e'.
    rewrite/swap_edge.
    case Heq: (e' == f)=> //.
    by move/eqP: Heq ->.
  Qed.

  Lemma imset_swap e f : 
    e \in E(G) -> 
    f \in E(G) ->
    c[E(G)] = (swap_edge e f)[E(G)].
  Proof.
    move=> He Hf; apply/setP=> c0.
    apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /swap_edge;
    exists (if e2 == e then f else if e2 == f then e else e2) => //;
    repeat case: ifP => //; repeat move=> /eqP -> //; try rewrite eq_refl //.
    - do 2 move=> _ -> //.
    - move=> _ /eqP -> //.
  Qed.

  (* TO DO: would be nice bc more info than previous, but longer and not sure how to finish *)
  Lemma perm_swap e f : 
    e \in E(G) -> 
    f \in E(G) ->
    perm_eq [seq c e' | e' <- enum E(G)] 
            [seq (swap_edge e f) e' | e' <- enum E(G)].
  Proof.
    move=> He Hf.
    apply/permP=> x.
    rewrite !count_map.
    have Hcount : forall P e' s, e' \in s -> count P s = count P (rem e' s) + (e'  \in s) && P e'.
    { 
      move=> P e' s He'; rewrite count_rem subnK //.
      case pe': (P e')=> //=.
      rewrite He' -has_count.
      by apply/hasP; exists e'; try rewrite mem_enum. 
    }
    rewrite -mem_enum in He.
    rewrite !(Hcount _ _ _ He) /=.
    case Hef: (e == f).
    - by rewrite (swap_edge_eq Hef) (eq_count (fun e' => congr1 x (swap_edge_eq Hef e'))).
    - admit.
  Admitted.

  (* Same proof as above*)
  Lemma imset_swap_vertex e f (x : G) :
    e \in E{x} -> 
    f \in E{x} -> 
    c[E{x}] = (swap_edge e f)[E{x}].
  Proof.
    move=> He0 He1; apply/setP=> c0.
    apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /swap_edge;
    exists (if e2 == e then f else if e2 == f then e else e2) => //;
    repeat case: ifP => //; repeat move=> /eqP -> //; try rewrite eq_refl //.
    - do 2 move=> _ -> //.
    - move=> _ /eqP -> //.
  Qed.

  (* TO DO: finish the rot_proper first, then complete this helper *)
  Lemma swap_proper_vertex (x y z : G) :
    is_proper_edge_coloring c ->
    (c [set x; y]) \in absent_set c z ->
    (c [set x; z]) \in absent_set c y ->
    is_proper_edge_coloring (swap_edge [set x; y] [set x; z]).
  Proof.
  Admitted.

End Recolor.
 
