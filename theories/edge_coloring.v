From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Setoid CMorphisms Relation_Definitions.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.
Require Import aux.
From Equations Require Import Equations.

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

  Lemma exists_v_of_c c x (c0 : ColorType) : 
    c0 \in c[E{x}] -> 
    exists y, ([set x; y] \in E(G)) && (c [set x; y] == c0).
  Proof.
    rewrite /edge_neigh /coloring_image => /imsetP[e] /imsetP[y].
    rewrite in_opn -in_edges => Hin He /eqP Hc; rewrite He eq_sym in Hc.
    by exists y. 
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
  
  Lemma is_proper_k_edge_coloring {k} (kc : k_edge_coloring k) :
    is_proper_edge_coloring kc.
  Proof. exact: proj2_sig (k_to_proper_coloring kc). Qed.

  Definition card_k_col {k} (kc : k_edge_coloring k) :
    #|kc[E(G)]| == k :=
   proj2_sig (projT2 kc).

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

  (* TODO: Should be straightforward, need to figure out which tactic to use8 *)
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

  (* arguably, could also work for matchings not just single edge *)
  (* Lemma del_edges_coloring (k : nat) :
    k_edge_colorable (del_edges del_e) k -> k_edge_colorable G (k + 1).
  Proof. 
    (* move=> Hpe [[ColorType [Hpc Hcard]]]. *)
    (* pose c' := extended_col Hpc. *)
    (* have Hp': is_proper_edge_coloring c' := proper_extended_col He. *)
      (* rewrite /c'. *)
    (* constructor. rewrite/k_edge_coloring. *)
    (* exists (option ColorType). *)
  Admitted. *)
End ExtendCol.

Section AbsentSet.
  Variables (G : sgraph).
  Implicit Types (x y : G).

  Definition absent_set {ColorType: finType} 
    (c : edge_coloring G ColorType) x :=
    setD (c[E(G)]) (c[E{x}]).

  (* still deciding on definitions further down, tbd which of these three will be needed *)
  (* Lemma absent_col {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x :
    c0 \in absent_set c x <-> [pick e in E{x} | c e == c0] == None.
  Proof. split=> H. Admitted. *)

  Lemma absent_edge {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x y :
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
    by rewrite subn_gt0 (eqP (card_k_col kc)) (leq_ltn_trans (leq_col_deg kc x)).
  Qed.
  
End AbsentSet.

Section Recolor.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (e f : {set G}).

  Definition recolor_edge e c0 : edge_coloring G ColorType :=
    fun edge => if edge == e then c0 else c edge.

  Lemma recolor_eq e c0 : (recolor_edge e c0) e = c0.
  Proof. by rewrite /recolor_edge eqxx. Qed.

  Lemma recolor_neq e f c0 : f != e -> (recolor_edge e c0) f = c f.
  Proof. by rewrite /recolor_edge=> /negPf ->. Qed.

  Lemma imset_recolor e c0 : 
    c[E(del_edges e)] = recolor_edge e c0 [E(del_edges e)].
  Proof.
    apply/setP => c1.
    by apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /recolor_edge;
    exists e2 => //; case: ifP => /eqP Heq //;
    rewrite Heq in He2; move: (del_edgesN e); rewrite -in_setC => /setCP.
  Qed.

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

  (* not needed right now *)
  (* Lemma del_edges_col c0 e : 
    (c0 \in c[E(G)]) ->
    (c0 != c e) ->
    (c0 \in c[E(del_edges e)]).
  Proof.
  Admitted. *)

  Lemma replace_col e c0 : 
    e \in E(G) ->  
    c0 \in c[E(del_edges e)] ->
    c e \notin c[E(del_edges e)] -> 
    #|recolor_edge e c0 [E(G)]| = #|c[E(G)]| - 1.
  Proof.
    move=> He.
    rewrite (del_edges1 He).
    move: (imset_recolor e c0).
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

Section Fan.
  Variable (G : sgraph) (ColorType : finType).
  Implicit Types (c : edge_coloring G ColorType) (v w : G) (e : {set G}) (f : seq G).

  (* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
  Definition neigh_prop v f := all (fun w => w \in N(v)) f.

  (* 2. if w0 is the first item in fan f centered at v under coloring c,
    (v, w0) is a distinct color from the rest of the edges in the graph *)
  (* Todo: two equivalent definitions, choose one *)
  Definition w0_prop 
    {ColorType} (c : edge_coloring G ColorType) e 
  := c e \notin c[E(del_edges e)].
    
  (* Definition w0_prop2 c e := 
    [forall (h : {set G} | (h \in E(G)) && (e != h)), c e != c h]. *)

  (* Todo: decide which w0_prop to use, they are equivalent *)
    (* Lemma w0_props c e : reflect (w0_prop1 c e) (w0_prop2 c e). *)
  (* Proof.  *)
  (* Admitted. *)

  Lemma w0_extended_col {e} (c_del : edge_coloring (del_edges e) ColorType)
  : w0_prop (extended_col c_del) e.
  Proof. 
    rewrite /w0_prop /extended_col eq_refl.
    by apply/negP => /imsetP [e' /del_edges1_neq /negbTE ->].
  Qed.

    (* 3. for all w_i, w_{i+1} in the fan f centered at v under coloring c,
    the color of (v, w_{i+1} is absent at w_i) *)
  Definition absent_prop c e w := 
    (c e) \in (absent_set c w).

  Definition fanp c f v wk := 
    uniq (wk::f) &&
    neigh_prop v (wk::f) &&
    w0_prop c [set v; (last wk f)] &&
    path (
      fun x2 => absent_prop c [set v; x2]
    ) wk f.

  Lemma fanp_w0_prop c f v wk : fanp c f v wk -> w0_prop c [set v; (last wk f)].
  Proof. by case/andP => /andP [_ ->] _. Qed.

  Lemma fanp_neigh c f v wk : fanp c f v wk -> neigh_prop v (wk::f).
  Proof. by case/andP => /andP [/andP [_ ->] _] _. Qed.

  Lemma rev_neigh f v wk : neigh_prop v (wk::f) -> neigh_prop v (rev (wk::f)).
  Proof. by rewrite /neigh_prop all_rev. Qed.

  Definition valid_fan_vertex {c f v wk} (fan : fanp c f v wk) (w : G) :=
    (w \in N(v)) && (w \notin wk::f) && absent_prop c [set v; w] wk.
  
  Lemma fan_cons {c f v wk} (fan : fanp c f v wk) (w : G) : 
    valid_fan_vertex fan w ->
    fanp c (wk::f) v w.
  Proof. 
    by move: fan;
    rewrite /fanp last_cons /neigh_prop /valid_fan_vertex
    => /andP[/andP[/andP[Hu Hn]] -> Hp] /andP[/andP[Hin Hnin] Ha].
  Qed.

End Fan.

Section Pack.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (c : edge_coloring G ColorType) (v w : G).

  Section FanDef.
    Variables (c : edge_coloring G ColorType) (v w : G).

    Record Fan : predArgType := { fval : seq G; _ : fanp c fval v w }.

    HB.instance Definition _ := [isSub for fval].
    HB.instance Definition _ := [Countable of Fan by <:].

  End FanDef.
End Pack.

Section FanOps.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (k : nat) (c : edge_coloring G ColorType) (fs : seq G).

  Fixpoint rotate c fs (v : G) : edge_coloring G ColorType :=
    match fs with
    | w0 :: ((w1::tl) as ws) =>
        rotate
            (swap_edge c [set v; w0] [set v; w1])
            ws v
    | _ => c
    end. 

  Lemma Fan_of_proof 
    {v w0 : G} 
    (c_del : edge_coloring (del_edges [set v; w0]) ColorType) 
  : v -- w0 -> fanp (extended_col c_del) [::] v w0.
  Proof.
    by rewrite /fanp (w0_extended_col c_del) -in_opn.
  Qed.

  Definition Fan_of_del_edges 
    {v w0 : G}
    (He : v -- w0)
    (c_del : edge_coloring (del_edges [set v; w0]) ColorType)
  := Build_Fan (Fan_of_proof c_del He).

  Lemma k_Fan_of_proof
    {k} {v w0 : G} 
    (He : [set v; w0] \in E(G))
    (kc_del : k_edge_coloring (del_edges [set v; w0]) k) 
  : fanp (k_extended_col He kc_del) [::] v w0.
  Proof.
    rewrite /fanp (w0_extended_col kc_del) //=.
    by have -> : w0 \in N(v) by move: (He); rewrite in_edges in_opn.
  Qed.

  (* TO THINK: Is there a way to avoid this (just use fan_of...) *)
  Definition k_Fan_of_del_edges 
    {k} {v w0 : G}
    (He : [set v; w0] \in E(G))
    (c_del : k_edge_coloring (del_edges [set v; w0]) k) 
  := Build_Fan (k_Fan_of_proof He c_del).
End FanOps.

Section Rotation. 
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v wk : G) (f : Fan c v wk).
  Implicit Type (w : G).

  Lemma fan_neigh : neigh_prop v (wk::val f).
  Proof. move: (valP f); exact: fanp_neigh. Qed.

  Lemma fan_w0_prop : w0_prop c [set v; (last wk (val f))].
  Proof. move: (valP f); exact: fanp_w0_prop. Qed.

  Lemma in_neigh w : w \in (wk::val f) -> w \in N(v).
  Proof. 
    move: fan_neigh; rewrite/neigh_prop=> /allP H. exact: H.
  Qed.

  Definition fancons {w} (H : valid_fan_vertex (valP f) w) := Build_Fan (fan_cons H).

  (* Lemma extend_absent :
    extend_fan = None ->   
    (forall wi, ~~ ((wi \in (wk :: val f)) && (c [set v; wi] == c [set v; wk]))) ->
    absent_prop c [set v; wk] v.
  Proof.
    rewrite/extend_fan.
    case: pickP=> [//|+ _].
  Admitted. *)

  Definition rotateF : edge_coloring G ColorType :=
    rotate c (rev (wk::val f)) v.

  Lemma imset_rot_vertex : c[E{v}] = rotateF[E{v}].
  Proof.
    rewrite /rotateF; set fs := (rev (wk::val f)).
    have Hws : neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [|w0 ws IH] d //= /andP [Hw0 Hws].
    case: ws IH Hws=> [|w1 wss IH] Hws //.
    rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //. 
    move/andP: Hws => [Hw1 _].
    have He0 : [set v; w0] \in E{v} by rewrite/edge_neigh; apply/imsetP; exists w0.
    have He1 : [set v; w1] \in E{v} by rewrite/edge_neigh; apply/imsetP; exists w1.
    exact: imset_swap_vertex He0 He1.
  Qed.

  (* Basically the same as above *)
  Lemma imset_rot : c[E(G)] = rotateF[E(G)].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [|w0 [|w1 wss] IH] d //= /andP [Hw0 Hws].
    rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //. 
    move/andP: Hws => [Hw1 _].
    have He0: [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    exact: imset_swap He0 He1.
  Qed.

  Lemma perm_rot : 
    perm_eq [seq c e | e <- enum E(G)] [seq rotateF e | e <- enum E(G)].
  Proof.
    rewrite /rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws => [|w0 [|w1 wss] IH] d //= /andP [Hw0 Hws].
    apply: (perm_trans _ (IH (swap_edge d [set v; w0] [set v; w1]) _)) => //.
    move/andP: Hws => [Hw1 _].
    have He0: [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    exact: perm_swap He0 He1.
  Qed.
  
  
  (* TO DO: could be more general too, bc will need to prove base case anyways *)
  Lemma imset_rot_del_edge (e0 e1 : {set G}) : 
    c e0 = rotateF e1 ->
    c[E(del_edges e0)] = rotateF[E(del_edges e1)].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [/=|w0 [|w1 wss] IH] d Hws.
    (* rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //.  *)
    (* move/andP: Hws => [Hw1 _].
    have He0: [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    exact: imset_swap He0 He1. *)
  Admitted.

  (* TO DO: Helper for next lemma, finish inductive step *)
  Lemma rot_first_last : c [set v; last wk (\val f)] = rotateF [set v; wk].
  Proof.
    rewrite /rotateF.
    set fs := \val f.
    elim: fs c=> [|w0 [|w1 wss] IH] d //=.
    - rewrite/swap_edge. case: ifP=> [/eqP -> //| H].
      by rewrite eq_refl.
    - admit.
  Admitted.

  Lemma rot_w0_prop : w0_prop rotateF [set v; wk].
  Proof.
    have +: w0_prop c [set v; (last wk (val f))] by exact: fan_w0_prop.
    rewrite/w0_prop.
    have Heq: c [E(del_edges [set v; last wk (\val f)])] = rotateF [E(del_edges [set v; wk])] 
      := imset_rot_del_edge rot_first_last. 
    by rewrite rot_first_last Heq.
  Qed.

  (* TO THINK: Arguably doesn't need to be it's own lemma *)
  Lemma card_rot :
    #|c[E(G)]| = #|rotateF[E(G)]|.
  Proof. by rewrite imset_rot. Qed.

  Lemma rot_absent_center : absent_set c v = absent_set rotateF v.
  Proof.
    by rewrite/absent_set imset_rot imset_rot_vertex.
  Qed.

  (* TO DO: may rephrase, can make it more/less general *)
  Lemma rot_absent_fan w c0 : 
    w \in (wk::val f) -> 
    c0 \in (absent_set c v :&: absent_set c w) ->
    c0 \in (absent_set rotateF v :&: absent_set rotateF w).
  Proof. 
  Admitted.

  (* TO DO: induction, b/c preserved at every step - how to reason ab fan properities after inductive step? set fseq := val f.
    move: f=> [fval Hfan]? *)
  Lemma rot_proper : 
    is_proper_edge_coloring c ->
    is_proper_edge_coloring rotateF.
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    elim: fs c=> [//|w0 ws IH] d Hd.
    case: ws IH=> [|w1 wss IH] //.
    specialize (IH (swap_edge d [set v; w0] [set v; w1])).
    (* rewrite -(IH (swap_edge d [set v; w0] [set v; w1])).  *)
  Admitted.

End Rotation.

Section MaximalFan.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v : G).
  Implicit Types (wk : G) (ck : ColorType).

  Definition is_fanmax {wk} (f : Fan c v wk) : Prop :=
    forall w, ~~ valid_fan_vertex (valP f) w.

  Equations fanmax {wk} (f : Fan c v wk) 
  : {w & Fan c v w} by wf #|N(v) :\: [set x in wk :: val f]| lt :=
    fanmax f := 
    match pickP (valid_fan_vertex (valP f)) with
      | Pick w Pw => fanmax (fancons Pw)
      | Nopick _ => existT _ wk f
    end.
  Next Obligation.
    apply/ltP/proper_card/properP. rewrite (set_cons w _).
    split.
    - exact/setDS/subsetU1. 
    - have /andP[/andP[Hin Hnin] _] := Pw.
      by exists w; rewrite 2!inE // in_set1 inE eq_refl Hin.
  Qed.

  Lemma fanmax_is_max {wk} (f : Fan c v wk)
  : is_fanmax (projT2 (fanmax f)).
  Proof.
    rewrite/is_fanmax=> w.
    funelim (fanmax f).
    case: pickP=> [wp Pw | Np].
    - exact (H wp Pw w).
    - by rewrite (Np w).
  Qed.

  (* For ck in A_c(wk) and c[E{v}], if we can't extend f then an edge on the fan is colored ck *)
  Lemma fanmax_present
    {ck} {wk} (f : Fan c v wk)
    (Hf : is_fanmax f)
    (Hnab : ck \notin absent_set c v)
    (Hab : ck \in absent_set c wk)
  :
    exists wj, 
    [&& [set v; wj] \in E(G), c [set v; wj] == ck & wj \in (wk :: val f)].
  Proof.
    have Hinc: ck \in c[E(G)] by rewrite/absent_set in_setD in Hab; exact: proj2 (andP Hab).
    have Hatv: ck \in c[E{v}] by exact: notin_setD Hinc Hnab.
    move: (exists_v_of_c Hatv)=> [wj] /andP[Hine /eqP Hc].
    exists wj; rewrite/is_fanmax in Hf; move: (Hf wj); rewrite/valid_fan_vertex.
    have -> : wj \in N(v) by rewrite in_opn -in_edges.
    by rewrite /absent_prop Hine Hc Hab eq_refl /= andbT negbK.
  Qed.

End MaximalFan.


Fixpoint alternates
  {G : sgraph} {ColorType : finType} 
  (c : edge_coloring G ColorType) (ca cb : ColorType) (p : seq G) : bool := 
  match p with 
  | x :: ((y :: tl) as p') =>
    (c [set x; y] == ca) && alternates c cb ca p'
  | _ => true
  end.

Section AltPath.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (x y z : G) (p : seq G) (ca cb : ColorType).

  Definition altpath ca cb x y p := alternates c ca cb (x::p) && upath x y p.
    (* (alternates c ca cb (x::p) || alternates c cb ca (x::p)) && upath x y p. *)

  Lemma altpathW ca cb x y p : altpath ca cb x y p -> pathp x y p.
  Proof.
    case/andP=> ap; apply (@upathW G x y p).
  Qed.
  
  Lemma altpathWW ca cb x y p : altpath ca cb x y p -> path (--) x p.
  Proof. by move/altpathW/pathpW. Qed.

  Lemma altpathxx ca cb x : altpath ca cb x x [ ::].
  Proof.
    by apply/andP; split.
  Qed.

  (* Lemma path_altpath {x y} ca cb (pth : Path x y) : 
    alternates c ca cb (x :: val pth) || alternates c cb ca (x :: val pth) && upath x y p
    -> altpath ca cb x y (val pth).
  Proof. 
    by move=> Ap; apply/andP; split=> //; exact: valP pth.
  Qed. *)

  Fixpoint next_col ca cb p : ColorType := 
    match p with 
    | _ :: p' => next_col cb ca p'
    | _ => cb
    end.
  Definition altpath_next_col {ca cb x y p} (ap : altpath ca cb x y p) := next_col ca cb p.
  (* if alternates c ca cb (x::p) then cb else ca. *)

  Lemma alternate_cons ca cb x y p :
    alternates c ca cb (x::y::p) = 
    (c [set x; y] == ca) && alternates c cb ca (y::p).
  Proof. by []. Qed.

  Lemma alternates_ca_cb ca cb x p:
    ((alternates c ca cb (x::p)) && (alternates c cb ca (x::p))) -> ((ca == cb) || (nilp p)).
  Proof.
    move: x; elim p=> [//| y p'] IH. 
    rewrite -{3}cat1s cat_nilp=> x.
    rewrite 2!alternate_cons=> /andP[/andP[/eqP Hca Hab] /andP[/eqP Hcb Hac]].
    by have ->: (ca == cb) by rewrite -Hca Hcb.
  Qed.

  (* Lemma altpath_cons ca cb x y z p : 
    altpath ca cb x y (z :: p) =
    [&& x -- z, c [set x; z] == ca & altpath cb ca z y p].
  Proof. 
    by rewrite /altpath alternate_cons pathp_cons andbCA -andbA.
  Qed. *)

  Lemma altpath_cons {ca cb y z p} x: 
    altpath ca cb x y (z::p) = [&& c [set x; z] == ca, altpath cb ca z y p, x -- z & x \notin (z::p)].
  Proof.
    by rewrite/altpath upath_cons alternate_cons -2!andbA (andbC (upath z y p)) (andbA (x -- z)).
  Qed.

  Lemma altpath_rcons ca cb x y z p: altpath ca cb x y (rcons p z) -> y = z.
  Proof. move/altpathW; exact: pathp_rcons. Qed.  

  (* Lemma altpath_cons {ca cb y z p} (ap : altpath ca cb y z p) x : 
    valid_altpath_vertex ap x -> 
    altpath ca cb x z (y :: p).
  Proof. 
    by move: ap;
    rewrite/altpath pathp_cons 2!alternate_cons/valid_altpath_vertex/next_col;
    move=> /andP[/orP[->|->] ->] /andP[-> Hc];
    first rewrite Hc;
    last case: ifP Hc=> _ ->.
  Qed. *)

End AltPath. 


Section AltPathDef.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (ca cb : ColorType) (x y : G).
  Record AltPath : predArgType := { aval : IPath x y; avalP : altpath c ca cb x y (nodes aval) }.

  HB.instance Definition _ := [isSub for aval].
  HB.instance Definition _ := [Countable of AltPath by <:].
  HB.instance Definition _ := [Finite of AltPath by <:].

  Definition ipath_of_altpath (p : AltPath) := aval p. 
  Definition in_altpath p x := x \in ipath_of_altpath p.
  
  Canonical AltPath_predType := Eval hnf in @PredType G AltPath in_altpath.
  Coercion ipath_of_altpath : AltPath >-> IPath.
End AltPathDef.

Section Kempe.
  Variables (G : sgraph) (ColorType : finType) (ca cb : ColorType).
  Implicit Types (x y z : G) (c : edge_coloring G ColorType) (pc : proper_edge_coloring G ColorType).
  
  (* singleton path *)
  Definition idap c x : AltPath c ca cb x x := Build_AltPath (altpathxx c ca cb x).

  (* Convert from path to altpath *)
  (* Definition apath_of {x y} (p : Path x y) (AH : alternates c ca cb (x :: val p)) : AltPath c ca cb x y := 
    Sub (val p) (path_altpath AH). *)

  Definition apcons 
    {c x y z} 
    {ap : AltPath c ca cb y z}
    (H : valid_altpath_vertex (valP ap) x)
  := Build_AltPath (altpath_cons H).

  Definition extend_ap {c x y} (ap : AltPath c ca cb x y) : option {w & AltPath c ca cb w y} := 
    match pickP (fun v => (v \in N(x)) && (c [set v; x] == next_col (valP ap))) with
    | Pick v Pv =>
        let Hv := prev_edge_proof (eq_rect (v \in N(x)) is_true (andP Pv).1 (x -- v) (in_opn v x)) in
        let Hc := (andP Pv).2 in
        Some (existT _ v (apcons Hv Hc))
    | Nopick _ => None
    end.
  
  (* Not needed right now *)
  (* Lemma extend_ap_none {c x y} (ap : AltPath c ca cb x y) : 
    extend_ap ap == None -> next_col (valP ap) \in absent_set c x.
  Proof. 
    rewrite /extend_ap; case pickP=> H _ //. 
    apply Nopick in H.
  Admitted. *)

  (* may use this as definition, or have it as lemma *)
  (* must be proper coloring and absent at start so no cycles when extended *)
  (* Definition apstart pc x y :=     
    { ap : AltPath pc ca cb x y | cb \in absent_set pc y}.

  Coercion apstart_to_altpath {pc x y} (aps : apstart pc x y) : 
    AltPath pc ca cb x y := projT1 aps. *)

  (* TO DO: Prove termination!! 
    what is the best way to do this? 
    current set-up would be fuel = total vertices of graph
    this is trickier than the fanmax case
    we need to prove there are no cycles to show we don't reuse vertices
    note this is only because we have a proper coloring
    so there is only one ca and one cb edge per vertex (one in, one out) at most
  *)
  Definition is_apmax {c y z} (ap : AltPath c ca cb y z) : Prop :=
    forall x, ~~ valid_altpath_vertex (valP ap) x.

  (* for proper edge colorings, this is equivalent to the above *)
  Definition is_apmax_abs {c y z} (ap : AltPath pc ca cb y z) : Prop :=
    next_col (valP ap) \in absent_set c y.

  Program Fixpoint apmax {pc x y} (d : nat) (ap : apstart pc x y) 
  : {v : G & apstart pc v y} :=
    match d with 
    | 0 => existT _ x ap
    | S d' => 
      match extend_ap ap with
      | Some (existT v ap') => apmax d' ap'
      | None => existT _ x ap
      end
    end.
  Next Obligation. exact: (projT2 ap). Defined.

  (*
  Definition kempe pc x := apmax (idap pc x).

  TO DO: define swap operation. Shouldn't be to complicated - use swap_edge and iterate through path
  Definition apswap (ap : AltPath c ca cb y z) :=  *)

End Kempe.

(* TO DO: finish up, nearly there. last little admits Hnotin' and Hprop'' may take a second *)
(* don't need cj \in c[E(G)] if we already know its in the absent set *)
Lemma smaller_coloring
  {G : sgraph} {v wj : G} {k}
  {c : k_edge_coloring G (k + 1)} 
  (f : Fan c v wj) (cj : projT1 c) :
  k = max_degree G + 1 ->
  cj \in (absent_set c v :&: absent_set c wj) ->
  k_edge_colorable G (max_degree G + 1).
Proof.
  move=> Hk Hcvw.
  have Hneigh : wj \in N(v) := (in_neigh (mem_head wj (val f))).
  have Hvw : [set v; wj] \in E(G).
  { by move: Hneigh; rewrite in_opn in_edges. }
  pose c' := rotateF f.
  have Hprop' : is_proper_edge_coloring c' := rot_proper (@is_proper_k_edge_coloring _ _ c).
  have Hin' : cj \in c'[E(del_edges [set v; wj])].
  { 
    rewrite in_setI in Hcvw; move/andP: (Hcvw)=> [Hcv _]; move: (Hcv).
    rewrite /absent_set (imset_rot f) (imset_rot_vertex f) /coloring_image/c'=> /setDP[/imsetP [ej Hej] Hcj _].
    rewrite (del_edges1 Hvw) in_setU1 in Hej; rewrite (rot_absent_center f) in Hcv.
    have Hneq: ej != [set v; wj] by move: (absent_edge Hcv Hneigh); rewrite Hcj; apply contra_neq=> ->.
    rewrite (negbTE Hneq) orFb in Hej.
    by apply/imsetP; exists ej.
  }
  have Hnotin': c'[set v; wj] \notin c'[E(del_edges [set v; wj])] by exact: rot_w0_prop.
  pose c'' := recolor_edge c' [set v; wj] cj.
  have Hprop'' := recolor_proper Hprop' (rot_absent_fan (mem_head wj (val f)) Hcvw).
  move: (replace_col Hvw Hin' Hnotin').
  rewrite -card_rot (eqP (card_k_col c)).
  have ->: k + 1 - 1 = max_degree G + 1 by rewrite Hk addn1 subn1.
  move=> Hcard''.
  by constructor; exists (projT1 c), (exist _ c'' Hprop''); rewrite Hcard''.
Qed.

(* TO DO *)
(* see edges_sum_degrees proof for example of induction on edges *)
Theorem Vizings (G : sgraph) (chi : nat): 
  is_chromatic_index G chi -> 
  max_degree G <= chi <= max_degree G + 1.
Proof.
  move=> Hchi; 
  rewrite chi_lower_bound //=.
  apply (chi_upper_bound_trans Hchi) => {Hchi}.
  elim/(size_ind (fun G => #|E(G)|)) : G => G IH.
  case: (set_0Vmem E(G)) => [E0|[e Ein]].
  - (* Base case #|E(G)| = 0 *)
    exists #|E(G)|.
    split; first by exact/inj_chrom.
    by rewrite E0 cards0.
  - (* Induction *)
    have [v [w0] [Edef Evw0]] := edgesP _ Ein; rewrite Edef in Ein; set G' := del_edges [set v; w0].
    have/IH [k' [[kc'] Hleqk']]: #|E(G')| < #|E(G)|.
    { by apply: proper_card; exact: del_edges_proper Ein _. }
    have: k' <= max_degree G + 1.
    { by apply/(leq_trans Hleqk'); rewrite leq_add2r; exact: del_edges_max_deg. }
    pose kc := k_extended_col Ein kc'.
    rewrite leq_eqVlt => /orP[/eqP Heqk'| Hltk']; first last.
    - (* if k' < max_degree G + 1, then we are done *) 
      exists (k' + 1).
      by split; [ |rewrite addn1].
    - pose f0 := k_Fan_of_del_edges Ein kc'.
      case Hfmax: (fanmax f0) => [w fmax].
      have tmp: (max_degree G + 1 <= k' + 1) by rewrite Heqk' (addn1 (max_degree G + 1)).
      move: (exists_absent_color kc tmp w) => {tmp} [c] Habw.
      case: (boolP (c \in absent_set kc v))=> Habv.
      - (* if c is absent at v, we can replace extra color with c *)
        have Hcap: (c \in absent_set kc v :&: absent_set kc w) by apply/setIP/(conj Habv Habw).
        by exists k'; rewrite Heqk'; move: (smaller_coloring fmax Heqk' Hcap).
      - have HfisMax : is_fanmax fmax by move: (fanmax_is_max f0); rewrite Hfmax /=. 
        have := (fanmax_present HfisMax Habv Habw)=> [[wj] Hwj].
      admit.
Admitted.


 
