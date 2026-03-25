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
  Definition edgeColoringType : Type := {set G} -> ColorType.
  Implicit Type (c : edgeColoringType).
  
  Definition is_proper_edge_coloring c : Prop := 
    forall (x : G),
    {in E{x}&, forall (e1 e2 : {set G}), c e1 = c e2 -> e1 = e2}.

  Definition properEdgeColoringType : Type := { c | is_proper_edge_coloring c }.
  Implicit Type (pc : properEdgeColoringType).

  Coercion proper_to_edge_coloring
    pc : edgeColoringType := proj1_sig pc.

  Lemma single_colored_proper pc {x y z : G} (xy : x -- y) (xz : x -- z) (c0 : ColorType) : 
    (sval pc) [set x; y] = c0 -> 
    ((sval pc) [set x; z] = c0) <-> (y = z).
  Proof.
    have := (proj2_sig pc); rewrite/is_proper_edge_coloring=> is_pc xy_c0.
    specialize (is_pc x [set x; y] [set x; z]).
    split=> [z_eq| <- //].
    rewrite z_eq in is_pc.
    by apply/(doubleton_eq_left x)/is_pc; try apply/edge_neigh_self.
  Qed.

  (* TO THINK: Should we remove this notation? It matches the write-up, but may just add confusion for the rocq code *)
  Definition coloring_image c (E : {set {set G}}) : {set ColorType} := c @: E.
  Local Notation "c [ E ]" := (coloring_image c E) (at level 50).

  Lemma in_c_edge_neighP c x (c0 : ColorType) : 
    reflect (exists2 y, [set x; y] \in E(G) & c [set x; y] = c0) (c0 \in c[E{x}]).
  Proof.
    rewrite/edge_neigh; apply/(iffP idP)=>[/imsetP[e] /imsetP[y]|[y] He Hc].
    - rewrite in_opn -in_edges=> Hin He Hc; rewrite He in Hc.
      by exists y.
    - apply/imsetP; exists [set x; y]=> //=.
      apply/imsetP; exists y; by rewrite // in_opn -in_edges He.
  Qed.
  
  Lemma in_c_all_edgeP c (c0 : ColorType) :
    reflect (exists2 e, e \in E(G) & c e = c0) (c0 \in c[E(G)]).
  Proof.
    apply/(iffP idP)=> [/imsetP[e] He /esym|[e] /edgesP [x] [y] [He Hxy]] Hc; first by exists e.
    rewrite -in_edges in Hxy; rewrite He in Hc.
    have: (c0 \in c[E{x}]) by apply/in_c_edge_neighP; exists y.
    rewrite -2!sub1set=> Hsub. 
    exact: (subset_trans Hsub (imsetS c (sub_all_edges x))).
  Qed.

  Lemma imset_c_del_edge c (e1 e2 : {set G}) :
    e1 \in E(G) -> e2 \in E(G) ->
    c e1 = c e2 -> 
    c [E(del_edges e1)] = c [E(del_edges e2)].
  Proof.
    rewrite/coloring_image=> e1_in_G e2_in_G eqc12.
    case: (boolP (e1 == e2))=> [/eqP ->//| neq12].
    apply/setP=> c0.
    wlog suff H : e1 e2 e1_in_G e2_in_G eqc12 neq12 /
    (c0 \in [set c e | e in E(del_edges e1)] ->
     c0 \in [set c e | e in E(del_edges e2)]).
    { 
      have H12 := H e1 e2 e1_in_G e2_in_G eqc12 neq12.
      rewrite eq_sym in neq12.
      have H21 := H e2 e1 e2_in_G e1_in_G (esym eqc12) neq12.
      apply/idP/idP; [exact: H12 | exact: H21].
    }
    move=> /imsetP [e3 e3_in_E eq03]; apply/imsetP.
    case: (boolP (e3 == e2))=> [/eqP eq23| neq23].
    - exists e1; last by rewrite eqc12 eq03 eq23.
      rewrite mem_del_edges e1_in_G.
      exact: edges_eqn_sub e1_in_G e2_in_G neq12.
    - exists e3; last by [].
      move: e3_in_E; rewrite 2!mem_del_edges=> /andP[e3_in_G _].
      rewrite e3_in_G.
      exact: edges_eqn_sub e3_in_G e2_in_G neq23.
  Qed. 

  Lemma leq_col_deg c x : #|c[E{x}]| <= max_degree G.
  Proof. 
    apply: (leq_trans (leq_imset_card _ _)).
    rewrite card_edge_neigh /max_degree.
    exact: leq_bigmax_cond.
  Qed.

  Lemma eq_deg_pcol pc x : #|pc[E{x}]| = #|E{x}|.
  Proof.
    apply: card_in_imset.
    exact: (proj2_sig pc). 
  Qed.

  Lemma leq_vertex_graph c x : #|c[E{x}]| <= #|c[E(G)]|.
  Proof.
    exact: subset_leq_card (imsetS c (sub_all_edges x)).
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
  Definition kEdgeColoringType k : Type := 
    { ColorType : finType &
      { c : properEdgeColoringType G ColorType | #|c[E(G)]| == k } }.

  Coercion k_to_proper_coloring {k} (kc : kEdgeColoringType k) : 
    properEdgeColoringType G (projT1 kc) :=
    proj1_sig (projT2 kc).

  Definition proper_to_k_coloring 
    {ColorType : finType} (pc : properEdgeColoringType G ColorType) 
  : kEdgeColoringType #|pc[E(G)]| := (existT _ ColorType (exist _ pc (eqxx _))).

  Definition card_k_col {k} (kc : kEdgeColoringType k) :
    #|kc[E(G)]| = k := eqP (proj2_sig (projT2 kc)).

  (* G is k-colorable if a k-edge-coloring exists. *)
  Definition k_edge_colorable k : Prop := inhabited (kEdgeColoringType k).

  (* The chromatic index chi is the smallest k such that G is k-colorable *)
  Definition is_chromatic_index chi : Prop :=
    k_edge_colorable chi /\ forall k, k < chi -> ~ k_edge_colorable k.

  (* We can already lower bound the chromatic index *)
  Theorem chi_lower_bound chi : 
    is_chromatic_index chi -> 
    max_degree G <= chi.
  Proof. 
    do 3![elim]=> ColorType is_chiEC _. 
    elim: is_chiEC=> ? /eqP <-.
    by rewrite leq_maxdeg_pcol.
  Qed.

  (* Any valid k-edge-coloring upper bounds chi *)
  Lemma chi_upper_bound k chi :
    is_chromatic_index chi ->
    k_edge_colorable k ->
    chi <= k.
  Proof.
    move=> [Hchi_color Hchi_min] kc.
    rewrite leqNgt.
    apply/negP=> Hlt.
    have nkc : ~ k_edge_colorable k := Hchi_min _ Hlt.
    exact: nkc kc.
  Qed.

  Lemma chi_upper_bound_trans k chi :   
    is_chromatic_index chi ->
    (exists n, k_edge_colorable n /\ n <= k) ->
    chi <= k.
  Proof.
    move=> ? [n] [? n_lt_k].
    have chi_lt_n : chi <= n by exact/chi_upper_bound.
    exact (leq_trans chi_lt_n n_lt_k).
  Qed.

  (* ----  One-to-one Coloring ---- *)

  (* injective coloring: each edge is a color *)
  Definition injEdgeColoringType : edgeColoringType G {set G} :=
    fun e => e.

  Definition proper_inj_coloring : properEdgeColoringType G {set G}.
  Proof.
    exists injEdgeColoringType.
    by move=> _ e1 e2 _ _ eq.
  Defined.

  Lemma imset_inj : proper_inj_coloring[E(G)] = E(G). 
  Proof.
    apply/setP=> e.
    apply/imsetP/idP=> [[e'] He' -> |He]; last by exists e.
    by rewrite /proper_inj_coloring /injEdgeColoringType.
  Qed.

  Definition inj_k_coloring : kEdgeColoringType #|E(G)|.
  Proof.
    exists {set G}, proper_inj_coloring; by rewrite imset_inj.
  Defined.

  (* Thus, all graphs have a k-edge-coloring with k = #|E(G)|*)
  Lemma inj_chrom : k_edge_colorable #|E(G)|.
  Proof.
    constructor; exact inj_k_coloring.
  Qed.

  (* If chi is a chromatic index of G, then chi <= |E(G)| *)
  Corollary chromatic_index_le_edges chi (is_chi : is_chromatic_index chi) :
    chi <= #|E(G)|.
  Proof.
    exact: (chi_upper_bound is_chi inj_chrom).
  Qed.

  (* TO THINK: could also prove chromatic index exists and is unique *)
End ChromIdx.

Section AbsentSet.
  Variables (G : sgraph).
  Implicit Types (x y : G).

  Definition absent_set {ColorType : finType} 
    (c : edgeColoringType G ColorType) x :=
    setD (c[E(G)]) (c[E{x}]).

  Lemma absent_in_imset {ColorType : finType} (c : edgeColoringType G ColorType) (c0 : ColorType) x :
    c0 \in absent_set c x -> c0 \in c[E(G)].
  Proof.
    by move=>/setDP [? _].
  Qed.

  Lemma absent_edge {ColorType : finType} (c : edgeColoringType G ColorType) (c0 : ColorType) x y :
    c0 \in absent_set c x -> y \in N(x) -> c0 != c [set x; y].
  Proof.
    move=> /setDP[_ /memPnC Hnin] ?.
    have in_cneigh : c [set x; y] \in c[E{x}].
    { by apply/imsetP; exists [set x; y]; first by apply/imsetP; exists y. }
    apply Hnin; exact: in_cneigh.
  Qed.

  Lemma absent_edge_sym {ColorType : finType} (c : edgeColoringType G ColorType) (c0 : ColorType) x y :
    c0 \in absent_set c x -> x \in N(y) -> c0 != c [set y; x].
  Proof. 
    have -> : [set y; x] = [set x; y] by rewrite doubleton_eq_iff; right.
    rewrite in_opn sg_sym -in_opn.
    exact: absent_edge. 
  Qed.

  Lemma absent_del_edge {ColorType : finType} (c : edgeColoringType G ColorType) x y z :
    [set x; y] \in E(G) -> x != z -> y != z ->
    c [set x; y] \notin c[E(del_edges [set x; y])] ->
    c [set x; y] \in absent_set c z.
  Proof.
    rewrite /absent_set=> xy_in xNz yNz w0p; apply/setDP; split;
    first by apply/imsetP; exists [set x; y].
    apply/negP=> /imsetP [e e_at_z cxy].
    apply: (negP w0p); apply/imsetP; exists e; last by [].
    rewrite mem_del_edges.
    apply/andP; split; 
    first by exact: (subsetP (sub_all_edges z) _ e_at_z).
    apply/subsetPn.
    move/edgesSetP: e_at_z => [w [-> _]].
    exists z; first by rewrite !inE eqxx.
    by rewrite !inE negb_or eq_sym xNz eq_sym.
  Qed.

  Proposition exists_absent_color {k : nat} (kc : kEdgeColoringType G k):
    max_degree G + 1 <= k ->
    forall x : G, exists c, c \in (absent_set kc x).
  Proof.
    rewrite addn1=> ? x; apply/set0Pn.
    rewrite -card_gt0 cardsDS; last by apply imsetS; apply sub_all_edges.
    by rewrite subn_gt0 (card_k_col kc) (leq_ltn_trans (leq_col_deg kc x)).
  Qed.
  
End AbsentSet.

Section ExtendCol. 
  Variables (G : sgraph) (del_e : {set G}) (He : del_e \in E(G)).

  Definition extendedColType 
    {ColorType : finType}
    (c : edgeColoringType (del_edges del_e) ColorType)
  : edgeColoringType G (option ColorType) :=
    fun e => if e == del_e then None else Some (c e).

  Lemma proper_extended_col
    {ColorType : finType}
    (pc : properEdgeColoringType (del_edges del_e) ColorType)
  : is_proper_edge_coloring (extendedColType pc).
  Proof.
    move:pc => [c Hp] x f0 f1 Hf0 Hf1.
    rewrite /extendedColType.
    case H00: (f0 == del_e); case H10 : (f1 == del_e) => //.
    - move/eqP: H00=> ->; move/eqP: H10 => -> //.
    move=> [Heq]; apply (Hp x); last by [];
    move/negbT: H00=> H00; move/negbT: H10=> H10;
    move/(subsetP (sub_all_edges x)): (Hf0)=> Hf0G;
    move/(subsetP (sub_all_edges x)): (Hf1)=> Hf1G;
    move: (edges_eqn_sub Hf0G He H00)=> Hsub0;
    move: (edges_eqn_sub Hf1G He H10)=> Hsub1;
    by rewrite (@del_edges_edge_neigh G del_e _ _).
  Qed.

  Lemma card_extended_col 
    {k : nat} 
    (kc : kEdgeColoringType (del_edges del_e) k) 
  : #|extendedColType kc[E(G)]| = k + 1.
  Proof. 
    rewrite /extendedColType /coloring_image.
    rewrite (del_edges1 He) imsetU1 eq_refl.
    have -> : [set (if e == del_e then None else Some ((sval (sval (projT2 kc))) e)) | e in E(del_edges del_e)]
            = Some @: (kc[E(del_edges del_e)]).
    {
      rewrite -imset_comp.
      apply/setP=> c0.
      apply/imsetP/imsetP=> [[e He' ->]| [e He' ->]];
      exists e=> //; rewrite ifF //;
      apply/negbTE/negP=> /eqP eEd;
      have := del_edgesN del_e; rewrite -{1}eEd;
      by rewrite He'.
    }
    rewrite cardsU1 card_imset; last by exact: Some_inj.
    rewrite card_k_col. 
    have -> : None \notin [set Some x | x in kc [E(del_edges del_e)]].
    { by apply/imsetP => [[x _ /eqP //]]. }
    by rewrite addnC.
  Qed.

  (* extendedColType of a k-edge-coloring produces a (k+1)-edge-coloring *)
  Definition k_extended_col 
    {k : nat}
    (kc : kEdgeColoringType (del_edges del_e) k)
  : kEdgeColoringType G (k + 1).
  Proof.
    exists (option (projT1 kc)), 
    (exist _ (extendedColType kc) (@proper_extended_col _ kc));
    by rewrite (card_extended_col kc). 
  Defined.

  Lemma extended_absent 
    {k : nat}
    {kc : kEdgeColoringType (del_edges del_e) k}
    {c0 : projT1 kc}
    {x : G}
  : c0 \in absent_set kc x -> Some c0 \in absent_set (k_extended_col kc) x.
  Proof.
    rewrite/absent_set=> /setDP[c0_in_kc c0_nin_kc].
    apply/setDP.
  Admitted.
  
End ExtendCol.

Section Recolor.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType).
  Implicit Types (e f : {set G}).

  Definition recolor_edge e c0 : edgeColoringType G ColorType :=
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
    rewrite/coloring_image/recolor_edge=> /imsetP [e1] e1_in_G def_c0.
    apply/subsetP=> c1 /imsetP [e2] e2_in_G.
    case: ifP=> _ def_c1; apply/imsetP;
    last by exists e2. 
    by exists e1; rewrite -def_c1 in def_c0.
  Qed.

  Lemma recolor_proper (x y : G) c0 :
    is_proper_edge_coloring c ->
    c0 \in (absent_set c x :&: absent_set c y) ->
    is_proper_edge_coloring (recolor_edge [set x; y] c0).
  Proof.
    rewrite/recolor_edge in_setI=> Hp /andP[Hax Hay].
    move: Hp=> Hp z e1 e2 Hz1 Hz2.
    move: (Hz1) (Hz2); rewrite/edge_neigh=> /imsetP [w1] Hw1 Ezw1 /imsetP [w2] Hw2 Ezw2.
    rewrite Ezw1 Ezw2.
    case: ifP=> /eqP /doubleton_eq_iff; 
    [case; move=> [H1 H2]|rewrite 4!(rwP eqP) !(rwP andP) (rwP orP) (rwP negP) negb_or];
    (case: ifP=> /eqP /doubleton_eq_iff; 
    [case; move=> [H3 H4]| rewrite 4!(rwP eqP) 2!(rwP andP) (rwP orP) (rwP negP) negb_or]);
    rewrite doubleton_eq_iff 5!(rwP eqP) 2!(rwP andP) (rwP orP).
    - by rewrite H2 H4 3!eq_refl. 
    - by rewrite H2 H4 -H3 H1 2!eq_refl.
    - rewrite -H1 in Hax=> _ /eqP Hc0.
      have Hcontra := absent_edge Hax Hw2. 
      by rewrite Hc0 eqxx in Hcontra.
    - by rewrite 2!eq_refl H2 -H3 H1 -H4 eq_refl.
    - by rewrite H2 H4 3!eq_refl.
    - rewrite -H1 in Hay=> _ /eqP Hc0.
      have Hcontra := absent_edge Hay Hw2. 
      by rewrite Hc0 eqxx in Hcontra.
    - rewrite -H3 in Hax=> _ /eqP Hc0.
      have Hcontra := absent_edge Hax Hw1. 
      by rewrite Hc0 eqxx in Hcontra.
    - rewrite -H3 in Hay=> _ /eqP Hc0.
      have Hcontra := absent_edge Hay Hw1. 
      by rewrite Hc0 eqxx in Hcontra.
    - rewrite Ezw1 in Hz1; rewrite Ezw2 in Hz2.
      rewrite eq_refl=> _ _ /eqP /(Hp z _ _ Hz1 Hz2) /doubleton_eq_left ->.
      by rewrite eq_refl.
  Qed.

  Lemma replace_col e c0 : 
    e \in E(G) ->  
    c0 \in c[E(del_edges e)] ->
    c e \notin c[E(del_edges e)] -> 
    #|recolor_edge e c0 [E(G)]| = #|c[E(G)]| - 1.
  Proof.
    move=> e_in_e.
    rewrite (del_edges1 e_in_e).
    move: (del_edges_imset_recolor e c0).
    rewrite /coloring_image 2!imsetU1 2!cardsU1 recolor_eq => -> -> -> /=.
    by rewrite add0n add1n subn1.
  Qed.

  Definition swap_edge e f : edgeColoringType G ColorType :=
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

  (* Same proof as above*)
  Lemma imset_swap_vertex e f (x : G) :
    e \in E{x} -> 
    f \in E{x} -> 
    c[E{x}] = (swap_edge e f)[E{x}].
  Proof.
    move=> He0 He1; apply/setP=> c0.
    apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /swap_edge;
    exists (if e2 == e then f else if e2 == f then e else e2) => //;
    repeat case: ifP=> //; repeat move=> /eqP -> //; try rewrite eq_refl //.
    - do 2 move=> _ -> //.
    - move=> _ /eqP -> //.
  Qed.

  Lemma imset_swap_nin e f (x : G) :
    x \notin e -> x \notin f ->
    c[E{x}] = (swap_edge e f)[E{x}].
  Proof.
    move=> x_nin_e x_nin_f; apply/setP=> c0.
    apply/imsetP/imsetP; move=> [e2 e2_in_G ->]; rewrite /swap_edge;
    exists e2=> //; move: e2_in_G; rewrite mem_edge_graph=> /andP[_ x_in_e2];
    by (case: ifP=> [/eqP contra|]; [by rewrite contra in x_in_e2; rewrite x_in_e2 in x_nin_e|]);
       (case: ifP=> [/eqP contra|]; [by rewrite contra in x_in_e2; rewrite x_in_e2 in x_nin_f|]).
  Qed.

  Lemma swap_absent_nin (e f : {set G}) (x : G) :
    x \notin e -> x \notin f -> e \in E(G) -> f \in E(G) ->
    absent_set (swap_edge e f) x = absent_set c x.
  Proof.
    rewrite/absent_set=> x_nin_e x_nin_f e_in_G f_in_G.
    by rewrite (imset_swap e_in_G f_in_G) (imset_swap_nin x_nin_e x_nin_f).
  Qed.

  Lemma swap_proper_vertex (x y z : G) :
    is_proper_edge_coloring c ->
    (c [set x; y]) \in absent_set c z ->
    (c [set x; z]) \in absent_set c y ->
    y \in N(x) -> z \in N(x) ->
    is_proper_edge_coloring (swap_edge [set x; y] [set x; z]).
  Proof.
    rewrite /is_proper_edge_coloring /swap_edge
      => pc abs_z abs_y y_at_x z_at_x u e1 e2  /edgesSetP [v1] [def_e1 uv1] /edgesSetP [v2] [def_e2 uv2].
    rewrite def_e1 def_e2.
    case: (boolP (v1 == v2))=> [/eqP ->| v1Nv2]; first by [].
    have [yNx zNx] : ((y == x) = false) /\ ((z == x) = false) by move: y_at_x z_at_x; do 2 rewrite in_opn sg_sym=> /sg_edgeNeq ->.
    (* case if (u, v1) = (x, y) *)
    case: ifP=> /eqP /doubleton_eq_iff.
    - move=> [[uEx v1Ey] | [uEy v1Ex]].
      + rewrite uEx in uv1 uv2 def_e1 def_e2 *.
        rewrite v1Ey in v1Nv2 uv1 def_e1 *.
        case: ifP=> [/eqP /doubleton_eq_left v2Ny | _]; first by rewrite v2Ny eq_refl in v1Nv2.
        case: ifP=> /eqP /doubleton_eq_left v2Ez /esym.
        * rewrite v2Ez in def_e2 uv2 *.
          exact: (pc x [set x; y] [set x; z] (edge_neigh_self uv1) (edge_neigh_self uv2)).
        * by rewrite in_opn in z_at_x=>   
            /(pc x [set x; v2] [set x; z] (edge_neigh_self uv2) (edge_neigh_self z_at_x)) /doubleton_eq_left.
      + rewrite uEy.
        case: ifP=> [/eqP /doubleton_eq_iff [[yEx _] | [_ ->]] | _];
          try rewrite v1Ex //; first by rewrite yEx eq_refl in yNx.
        case: ifP=> [/eqP /doubleton_eq_iff | _].
        * rewrite 4!(rwP eqP) 2!(rwP andP) yNx -v1Ex=> /orP. 
          rewrite /= => /andP[_ /eqP v1Ev2]; by rewrite v1Ev2 eq_refl in v1Nv2.
        * rewrite -in_opn uEy in uv2=> cEc.
          have := absent_edge abs_y uv2; by rewrite cEc eq_refl.
    - case: ifP=> /eqP /doubleton_eq_iff.
      + move=> [[uEx v1Ez] | [uEz v1Ex]].
        * rewrite uEx v1Ez in uv1 uv2 *.
          case: ifP=> [/eqP /doubleton_eq_left v2Ey _ /esym|];
          first by rewrite v2Ey in uv2 *; exact: (pc x [set x; z] [set x; y] (edge_neigh_self uv1) (edge_neigh_self uv2)).
          case: ifP=> [/eqP /doubleton_eq_left -> //|_ /eqP /doubleton_eq_left v2Ny _].
          by rewrite in_opn in y_at_x
            => /(pc x _ _ (edge_neigh_self y_at_x) (edge_neigh_self uv2)) /doubleton_eq_left /esym.
        * rewrite uEz in uv2 *.
          case: ifP=>[/eqP /doubleton_eq_iff _ _ cEc|];
          first by have := absent_edge_sym abs_z z_at_x; rewrite cEc eq_refl.
          case: ifP=> [/eqP /doubleton_eq_iff|_ _ _ cEc];
          last by rewrite -in_opn in uv2; have := absent_edge abs_z uv2; rewrite cEc eq_refl.
          rewrite 4!(rwP eqP) 2!(rwP andP) zNx -v1Ex eq_refl=> /orP.
          rewrite /= => /eqP v1Ev2. 
          by rewrite v1Ev2 eq_refl in v1Nv2.
      + case: ifP=> [/eqP /doubleton_eq_iff [[uEx v2Ey] | [uEy v2Ex]] + + cEc|].
        -- rewrite uEx v2Ey in uv1 cEc *.
           rewrite in_opn in z_at_x.
           have /doubleton_eq_left -> := pc x _ _ (edge_neigh_self uv1) (edge_neigh_self z_at_x) cEc.
           by rewrite 4!(rwP eqP) 2!(rwP andP) 2!eq_refl=> /orP.
        -- rewrite uEy in uv1 cEc *.
           rewrite -in_opn in uv1.
           have := absent_edge abs_y uv1.
           by rewrite cEc eq_refl.
        * case: ifP=>[/eqP /doubleton_eq_iff [[uEx v2Ez] | [uEz v2Ex]] + + +|_ _ _ _] cEc.
        -- rewrite uEx v2Ez in uv1 cEc * => _ _.
           rewrite in_opn in y_at_x.
           have /doubleton_eq_left -> := pc x _ _ (edge_neigh_self uv1) (edge_neigh_self y_at_x) cEc.
           by rewrite 4!(rwP eqP) 2!(rwP andP) 2!eq_refl=> /orP.
        -- rewrite uEz in uv1 cEc *.
           rewrite -in_opn in uv1.
           have := absent_edge abs_z uv1.
           by rewrite cEc eq_refl.
    exact: (pc u _ _ (edge_neigh_self uv1) (edge_neigh_self uv2) cEc). 
  Qed.

End Recolor.
 
