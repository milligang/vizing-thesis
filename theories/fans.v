From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Fan.
  Variable (G : sgraph) (ColorType : finType).
  Implicit Types (c : edgeColoringType G ColorType) (v wk w : G) (e : {set G}) (f : seq G).

  (* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
  Definition neigh_prop v f := all (fun w => w \in N(v)) f.

  (* 2. if w0 is the first item in fan f centered at v under coloring c,
    (v, w0) is a distinct color from the rest of the edges in the graph *)
  Definition w0_prop 
    {ColorType} (c : edgeColoringType G ColorType) e 
  := c e \notin c[E(del_edges e)].

  Lemma w0_prop_extended {e} (c_del : edgeColoringType (del_edges e) ColorType)
  : w0_prop (extendedColType c_del) e.
  Proof. 
    rewrite /w0_prop /extendedColType eq_refl.
    by apply/negP => /imsetP [e' /del_edges1_neq /negbTE ->].
  Qed.

  Lemma w0_col_extended {e} (c_del : edgeColoringType (del_edges e) ColorType)
  : (extendedColType c_del) e = None.
  Proof. by rewrite /extendedColType eq_refl. Qed.

  Lemma swap_w0 {c e1 e2} (He1: e1 \in E(G)) (He2: e2 \in E(G))
  : w0_prop c e1 -> w0_prop (swap_edge c e1 e2) e2.
  Proof.
    rewrite/w0_prop/coloring_image.
    case: (boolP (e1 == e2))=> [/eqP ->| e1Ne2].
    - have /(swap_edge_eq c) sEc: e2 == e2 by trivial.
      by rewrite sEc (eq_imset _ sEc).
    move=> /memPnC h.
    apply/memPnC=> c0 /imsetP [e] He ->.
    have ->: swap_edge c e1 e2 e2 = c e1 by rewrite/swap_edge eq_sym (negbTE e1Ne2) eqxx.
    apply: h.
    case: (boolP (e == e1))=> [/eqP ->| eNe1].
    - have ->: swap_edge c e1 e2 e1 = c e2 by rewrite/swap_edge eqxx.
      apply: imset_f.
      rewrite mem_del_edges He2 (edges_eqn_sub He2 He1) //.
      by rewrite eq_sym.
    have eNe2: e != e2 := del_edges1_neq He.
    have ->: swap_edge c e1 e2 e = c e by rewrite/swap_edge (negbTE eNe1) (negbTE eNe2).
    apply: imset_f.
    move: He.
    rewrite 2! mem_del_edges=> /andP[e_in_G _].
    rewrite e_in_G; apply (edges_eqn_sub e_in_G He1 eNe1).
  Qed.

  (* 3. for all w_i, w_{i+1} in the fan f centered at v under coloring c,
    the color of (v, w_{i+1} is absent at w_i) *)
  Definition absent_prop c e w := 
    (c e) \in (absent_set c w).

  Definition fanp c f v w0 wk := 
    (last wk f == w0) && 
    uniq (wk::f) &&
    neigh_prop v (wk::f) &&
    w0_prop c [set v; w0] &&
    path (
      fun x2 => absent_prop c [set v; x2]
    ) wk f.

  Lemma fanpW c f v w0 wk : fanp c f v w0 wk -> path (fun x2 => absent_prop c [set v; x2]) wk f.
  Proof. by case/andP. Qed.

  Lemma fanpW_rev c f v w0 wk : 
    fanp c f v w0 wk -> 
    path (fun x2 x1 => absent_prop c [set v; x1] x2) (last wk f) (rev (belast wk f)).
  Proof.
    move=> /fanpW. by rewrite rev_path.
  Qed.

  Lemma fanp_last c f v w0 wk : fanp c f v w0 wk -> last wk f = w0.
  Proof. by case/andP=> /andP[/andP[/andP[/eqP-> _] _] _] _. Qed.

  Lemma fanp_uniq c f v w0 wk : fanp c f v w0 wk -> uniq (wk::f).
  Proof. by case/andP=> /andP[/andP[/andP[_ ->] _] _]. Qed.

  Lemma fanp_w0_prop c f v w0 wk : fanp c f v w0 wk -> w0_prop c [set v; w0].
  Proof. by case/andP=> /andP [_ ->] _. Qed.

  Lemma fanp_neigh c f v w0 wk : fanp c f v w0 wk -> neigh_prop v (wk::f).
  Proof. by case/andP => /andP [/andP [_ ->] _] _. Qed.

  Lemma rev_neigh f v wk : neigh_prop v (wk::f) -> neigh_prop v (rev (wk::f)).
  Proof. by rewrite /neigh_prop all_rev. Qed.

  Definition valid_fan_vertex {c f v w0 wk} (fan : fanp c f v w0 wk) (w : G) :=
    (w \in N(v)) && (w \notin wk::f) && absent_prop c [set v; w] wk.
  
  Lemma fanp_cons {c f v w0 wk} (fan : fanp c f v w0 wk) (w : G) : 
    valid_fan_vertex fan w ->
    fanp c (wk::f) v w0 w.
  Proof. 
    by move: fan;
    rewrite /fanp last_cons /neigh_prop /valid_fan_vertex
    => /andP[/andP[/andP[/andP[Hl Hu] Hn]] -> Hp] /andP[/andP[Hin Hnin] Ha].
  Qed.

  Lemma sub_fanp 
    {c f v w0 wk}
    {f1 f2 : seq G} {w}
    (Hcat : (wk::f) = f1 ++ (w :: f2))
  : fanp c f v w0 wk -> fanp c f2 v w0 w.
  Proof.
    rewrite/fanp -(last_cons wk wk) Hcat cat_uniq /neigh_prop all_cat -cat_rcons last_cat last_rcons
    => /andP[/andP[/andP[/andP[-> /andP[_ /andP[_ ->]]] /andP[_ ->]] ->] +].
    case: f1 Hcat=> [|wk' f1].
    - by rewrite cat0s; case=> <- <-.
    - rewrite cat_cons; case=> _ ->.
      by rewrite -cat_rcons cat_path last_rcons=> /andP[_ ->].
  Qed.

  Lemma swap_fanp c f v w0 wk : 
    fanp c f v w0 wk -> 
    fanp (swap_edge c [set v; w0] [set v; last wk (belast wk f)]) (behead (belast wk f)) v (last wk (belast wk f)) wk.
  Proof.
    rewrite/fanp=> /andP[/andP[/andP[/andP[Hlast Huniq] Hneigh] Hw0] Hpath].
    have w0_in_G: [set v; w0] \in E(G).
    {
      rewrite in_edges -in_opn.
      move/allP: Hneigh=> Hneigh.
      apply Hneigh.
      move/eqP: Hlast=> <-.
      apply mem_last.
    }
    move: Hneigh=> /andP[Hwk Hneigh].
    have wk_in_G: [set v; wk] \in E(G) by rewrite in_edges -in_opn.
    have := lastI wk f.
    (* elim: f1=> [|w1 ws IH] /=;
    first by rewrite Hwk eq_refl (swap_w0 w0_in_G wk_in_G Hw0). 
    have fcat : f = behead f1 ++ [::w0] by admit.
    rewrite/fanp.
    rewrite fcat.
    move=> /andP[/andP[/andP[/andP[A B] C] L] H]. *)
  Admitted.

End Fan.

Section Pack.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (c : edgeColoringType G ColorType) (v w : G).

  Section FanDef.
    Variables (c : edgeColoringType G ColorType) (v w0 w : G).

    Record Fan : predArgType := { fval : seq G; _ : fanp c fval v w0 w }.

    HB.instance Definition _ := [isSub for fval].
    HB.instance Definition _ := [Countable of Fan by <:].

  End FanDef.
End Pack.

Section FanOps.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (k : nat) (c : edgeColoringType G ColorType) (fs : seq G).

  Fixpoint rotate c fs (v : G) : edgeColoringType G ColorType :=
    match fs with
    | w0 :: ((w1::tl) as ws) =>
        rotate
            (swap_edge c [set v; w0] [set v; w1])
            ws v
    | _ => c
    end. 

  Lemma Fan_of_proof 
    {v w0 : G} 
    (c_del : edgeColoringType (del_edges [set v; w0]) ColorType) 
  : v -- w0 -> fanp (extendedColType c_del) [::] v w0 w0.
  Proof.
    by rewrite /fanp (w0_prop_extended c_del) -in_opn.
  Qed.

  Definition Fan_of_del_edges 
    {v w0 : G}
    (He : v -- w0)
    (c_del : edgeColoringType (del_edges [set v; w0]) ColorType)
  := Build_Fan (Fan_of_proof c_del He).

  Lemma k_Fan_of_proof
    {k} {v w0 : G} 
    (He : [set v; w0] \in E(G))
    (kc_del : kEdgeColoringType (del_edges [set v; w0]) k) 
  : fanp (k_extended_col He kc_del) [::] v w0 w0.
  Proof.
    rewrite /fanp (w0_prop_extended kc_del) //=.
    by have -> : w0 \in N(v) by move: (He); rewrite in_edges in_opn.
  Qed.

  (* TO THINK: Is there a way to avoid this (just use fan_of...) *)
  Definition k_Fan_of_del_edges 
    {k} {v w0 : G}
    (He : [set v; w0] \in E(G))
    (kc_del : kEdgeColoringType (del_edges [set v; w0]) k) 
  := Build_Fan (k_Fan_of_proof He kc_del).
End FanOps.

Section Rotation. 
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (v w0 wk : G) (f : Fan c v w0 wk).
  Implicit Type (w : G).

  Lemma fanW : path (fun x2 => absent_prop c [set v; x2]) wk (fval f).
  Proof. move: (valP f); exact: fanpW. Qed.

  Lemma fan_last : last wk (val f) = w0.
  Proof. move: (valP f); exact: fanp_last. Qed.

  Lemma fan_rev : rev (wk::val f) = w0::(rev (belast wk (fval f))).
  Proof. rewrite lastI rev_rcons. congr (_ :: _). exact: fan_last. Qed.

  Lemma fanW_rev : path (fun x2 x1 => absent_prop c [set v; x1] x2) w0 (rev (belast wk (fval f))).
  Proof. move: (valP f)=> /fanpW_rev. by rewrite fan_last. Qed.

  Lemma fan_uniq : uniq (wk::val f).
  Proof. move: (valP f); exact: fanp_uniq. Qed.

  Lemma fan_neigh : neigh_prop v (wk::val f).
  Proof. move: (valP f); exact: fanp_neigh. Qed.

  Lemma fan_w0_prop : w0_prop c [set v; w0].
  Proof. move: (valP f); exact: fanp_w0_prop. Qed.

  Lemma in_neigh w : w \in (wk::val f) -> w \in N(v).
  Proof. 
    move: fan_neigh; rewrite/neigh_prop=> /allP H. exact: H.
  Qed.

  Definition fancons {w} (H : valid_fan_vertex (valP f) w) := Build_Fan (fanp_cons H).

  Lemma sub_fan {f1 f2 : seq G} w (Hcat : (wk::val f) = f1 ++ (w :: f2)) : Fan c v w0 w.
  Proof.
    move: (valP f)=> Hf. exact: (Build_Fan (sub_fanp Hcat Hf)). 
  Qed.

  Lemma swap_fan : 
    Fan (swap_edge c [set v; w0] [set v; last wk (belast wk (val f))]) v (last wk (belast wk (val f))) wk.
  Proof. move: (valP f)=> Hf; exact: (Build_Fan (swap_fanp Hf)). Qed.

  Definition rotateF : edgeColoringType G ColorType :=
    rotate c (rev (wk::val f)) v.

  Lemma rot_notin (e : {set G}) :
    e \in E(G) -> e \notin E{v} -> c e = rotateF e.
  Proof.
    rewrite /rotateF mem_edge_graph=> -> /= e_nin_v; set fs := (rev (wk::val f)).
    elim: fs c=> [|w1 [|w2 wss] IH] d //.
    change (d e = rotate (swap_edge d [set v; w1] [set v; w2]) (w2 :: wss) v e).
    rewrite -(IH (swap_edge d [set v; w1] [set v; w2])).
    rewrite /swap_edge. move: e_nin_v.
    case: ifP=> [/eqP -> /negP|]; first by rewrite set21.
    case: ifP=> [/eqP -> /negP|//]; by rewrite set21.
  Qed.

  Lemma imset_rot_vertex : c[E{v}] = rotateF[E{v}].
  Proof.
    rewrite /rotateF; set fs := (rev (wk::val f)).
    have Hws : neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [|w1 ws IH] d //= /andP [Hw1 Hws].
    case: ws IH Hws=> [|w2 wss IH] Hws //.
    rewrite -(IH (swap_edge d [set v; w1] [set v; w2])) //. 
    move/andP: Hws => [Hw2 _].
    have He1 : [set v; w1] \in E{v} by rewrite/edge_neigh; apply/imsetP; exists w1.
    have He2 : [set v; w2] \in E{v} by rewrite/edge_neigh; apply/imsetP; exists w2.
    exact: imset_swap_vertex He1 He2.
  Qed.

  (* Basically the same as above *)
  Lemma imset_rot : c[E(G)] = rotateF[E(G)].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [|w1 [|w2 wss] IH] d //= /andP [Hw1 Hws].
    rewrite -(IH (swap_edge d [set v; w1] [set v; w2])) //. 
    move/andP: Hws => [Hw2 _].
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    have He2: [set v; w2] \in E(G) by rewrite in_opn -in_edges in Hw2.
    exact: imset_swap He1 He2.
  Qed.

  Lemma imset_rot_del_edge (e0 e1 : {set G}) : 
    e0 \in E(G) -> e1 \in E(G) ->  
    c e0 = rotateF e1 ->
    c[E(del_edges e0)] = rotateF[E(del_edges e1)].
  Proof.
    rewrite /coloring_image=> e0_in_G e1_in_G.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    elim: fs c=> [/=|w1 [/=|w2 wss] IH] d.
    - exact: imset_c_del_edge. 
    - exact: (IH d). 
    rewrite -[rotate d [:: w1,  w2  & wss] v]/(rotate (swap_edge d [set v; w1] [set v; w2]) (w2 :: wss) v)=> de0.
    specialize (IH (swap_edge d [set v; w1] [set v; w2])).
  Admitted.

  Lemma rotate_last (fs : seq G) (d : edgeColoringType G ColorType) :
      d [set v; head w0 fs] = rotate d fs v [set v; last w0 fs].
  Proof.
    elim: fs d=> [/=|w1 [|w2 wss] IH] d'; try by [].
    change (d' [set v; w1] = rotate (swap_edge d' [set v; w1] [set v; w2]) (w2 :: wss) v [set v; last w2 wss]).
    rewrite -(IH (swap_edge d' [set v; w1] [set v; w2])) /=.
    rewrite /swap_edge; 
    case: ifP=> [/eqP /doubleton_eq_left -> //|].
    by rewrite eq_refl.
  Qed.

  Lemma rot_first_last : c [set v; w0] = rotateF [set v; wk].
  Proof.
    rewrite /rotateF. 
    set fs := (rev (wk::val f)).
    have -> : w0 = (head w0 fs) by rewrite /fs fan_rev.
    have -> : wk = (last w0 fs) by rewrite /fs rev_cons last_rcons.
    exact: (rotate_last fs c). 
  Qed.

  Lemma rot_w0_prop : w0_prop rotateF [set v; wk].
  Proof.
    have +: w0_prop c [set v; w0] by exact: fan_w0_prop.
    rewrite/w0_prop.
    have vw0_in_G : [set v; w0] \in E(G).
    {
      rewrite in_edges -in_opn.
      apply/in_neigh.
      by have := mem_last wk (\val f); rewrite fan_last.
    }
    have vwk_in_G : [set v; wk] \in E(G).
    {
      rewrite in_edges -in_opn.
      apply/in_neigh.
      by rewrite mem_head.
    }
    have Heq: c [E(del_edges [set v; w0])] = rotateF [E(del_edges [set v; wk])] 
      := imset_rot_del_edge vw0_in_G vwk_in_G rot_first_last. 
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

  Lemma rot_absent_fan w c0 : 
    w \in (wk::val f) -> 
    c0 \in (absent_set c v :&: absent_set c w) ->
    c0 \in (absent_set rotateF v :&: absent_set rotateF w).
  Proof. 
    rewrite /absent_set imset_rot imset_rot_vertex=> /in_neigh w_at_v /setIP[/setDP[c0_in_r c0_nin_v] /setDP[_ /negP c0_nin_w]].
    apply/setIP; split; apply/setDP; split; try by assumption.
    apply/negP=> /imsetP [e /edgesSetP [y] [def_e wy]] cNr.
    have /andP[/andP[e_at_w e_at_y] wNy] : (e \in E{G;w}) && (e \in E{G;y}) && (w != y) by apply/edge_neigh_edge; rewrite def_e wy.
    apply: c0_nin_w. 
    have e_in_E : [set w; y] \in E(G)  by move: e_at_w; rewrite mem_edge_graph def_e=> /andP[-> _].
    apply/in_c_edge_neighP; exists y=> //.
    case: (boolP (y == v)) => [/eqP yEv | yNv].
    - exfalso. move: c0_nin_v=> /negP c0_nin_v. 
      apply: c0_nin_v. apply/in_c_edge_neighP; rewrite -yEv.
      have set_refl : [set w; y] = [set y; w] by apply/doubleton_eq_iff; right.
      rewrite set_refl in def_e e_in_E.
      exists w=> //.
      by rewrite cNr def_e. 
    rewrite cNr def_e. 
    apply/rot_notin/negP=>// /imsetP [x] x_at_v /doubleton_eq_iff [[wEv yEx] | [_ yEv]].
    - move: w_at_v. by rewrite in_opn=> /sg_edgeNeq; rewrite wEv eq_refl.
    by rewrite yEv eq_refl in yNv.
  Qed.

  Lemma rot_proper : 
    is_proper_edge_coloring c ->
    is_proper_edge_coloring rotateF.
  Proof.
    rewrite/rotateF fan_rev.
    set fs := rev (belast wk (val f)).
    have nps: neigh_prop v (w0 :: fs) by rewrite /fs -fan_rev; apply rev_neigh; exact: fan_neigh.
    have abs_fs: path (fun x2 x1 => absent_prop c [set v; x1] x2) w0 fs := fanW_rev; rewrite /absent_prop in abs_fs.
    have w0p: w0_prop c [set v; w0] := fan_w0_prop; rewrite /w0_prop in w0p.
    elim: fs c w0 abs_fs w0p nps => [//|w1 [|w2 wss] IH] d x0 /andP[abs_w01 abs_fs] x0p /andP[x0_at_v /andP[w1_at_v nps]] pc_d.
    - rewrite/rotate. apply/(swap_proper_vertex pc_d (absent_del_edge _ _ _ _) abs_w01 x0_at_v w1_at_v); rewrite //=; first by rewrite in_edges -in_opn.
      + by move: w1_at_v; rewrite in_opn=> /sg_edgeNeq ->.
      + apply/negP=> /eqP eq. 
        have : d [set v; w1] != d [set v; x0] := absent_edge_sym abs_w01 x0_at_v.
        by rewrite eq eqxx.
    apply: (IH (swap_edge d [set v; x0] [set v; w1]) w1).
    - admit.
    - admit.
    - admit.
    have abs_x01: d [set v; x0]  \in absent_set d w1 by admit.
    exact (swap_proper_vertex pc_d abs_x01 abs_w01 x0_at_v w1_at_v).
  Admitted.

End Rotation.

Section MaximalFan.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (v w0 : G).
  Implicit Types (wk : G) (ck : ColorType).

  Definition is_fanmax {wk} (f : Fan c v w0 wk) : Prop :=
    forall w, ~~ valid_fan_vertex (valP f) w.

  Equations fanmax {wk} (f : Fan c v w0 wk) 
  : {w & Fan c v w0 w} by wf #|N(v) :\: [set x in wk :: val f]| lt :=
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

  Lemma fanmax_is_max {wk} (f : Fan c v w0 wk)
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
    {ck} {wk} (f : Fan c v w0 wk)
    (Hf : is_fanmax f)
    (Hnab : ck \notin absent_set c v)
    (Hab : ck \in absent_set c wk)
  :
    exists wj, 
    [&& [set v; wj] \in E(G), c [set v; wj] == ck & wj \in (wk :: val f)].
  Proof.
    have Hinc: ck \in c[E(G)] by rewrite/absent_set in_setD in Hab; exact: proj2 (andP Hab).
    have Hatv: ck \in c[E{v}] by exact: notin_setD Hinc Hnab.
    move/in_c_edge_neighP: Hatv=> [wj] Hine Hc.
    exists wj; rewrite/is_fanmax in Hf; move: (Hf wj); rewrite/valid_fan_vertex.
    have -> : wj \in N(v) by rewrite in_opn -in_edges.
    by rewrite /absent_prop Hine Hc Hab eq_refl /= andbT negbK.
  Qed.

End MaximalFan.