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
  Implicit Types (c : edge_coloring G ColorType) (v wk w : G) (e : {set G}) (f : seq G).

  (* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
  Definition neigh_prop v f := all (fun w => w \in N(v)) f.

  (* 2. if w0 is the first item in fan f centered at v under coloring c,
    (v, w0) is a distinct color from the rest of the edges in the graph *)
  (* Todo: two equivalent definitions, choose one *)
  Definition w0_prop 
    {ColorType} (c : edge_coloring G ColorType) e 
  := c e \notin c[E(del_edges e)].

  Lemma w0_prop_extended {e} (c_del : edge_coloring (del_edges e) ColorType)
  : w0_prop (extended_col c_del) e.
  Proof. 
    rewrite /w0_prop /extended_col eq_refl.
    by apply/negP => /imsetP [e' /del_edges1_neq /negbTE ->].
  Qed.

  Lemma w0_col_extended {e} (c_del : edge_coloring (del_edges e) ColorType)
  : (extended_col c_del) e = None.
  Proof. by rewrite /extended_col eq_refl. Qed.

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

  Lemma fanp_last c f v w0 wk : fanp c f v w0 wk -> last wk f = w0.
  Proof. by case/andP=> /andP[/andP[/andP[/eqP-> _] _] _] _. Qed.

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

End Fan.

Section Pack.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (c : edge_coloring G ColorType) (v w : G).

  Section FanDef.
    Variables (c : edge_coloring G ColorType) (v w0 w : G).

    Record Fan : predArgType := { fval : seq G; _ : fanp c fval v w0 w }.

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
  : v -- w0 -> fanp (extended_col c_del) [::] v w0 w0.
  Proof.
    by rewrite /fanp (w0_prop_extended c_del) -in_opn.
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
  : fanp (k_extended_col He kc_del) [::] v w0 w0.
  Proof.
    rewrite /fanp (w0_prop_extended kc_del) //=.
    by have -> : w0 \in N(v) by move: (He); rewrite in_edges in_opn.
  Qed.

  (* TO THINK: Is there a way to avoid this (just use fan_of...) *)
  Definition k_Fan_of_del_edges 
    {k} {v w0 : G}
    (He : [set v; w0] \in E(G))
    (kc_del : k_edge_coloring (del_edges [set v; w0]) k) 
  := Build_Fan (k_Fan_of_proof He kc_del).
End FanOps.

Section Rotation. 
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v w0 wk : G) (f : Fan c v w0 wk).
  Implicit Type (w : G).

  Lemma fanW : path (fun x2 => absent_prop c [set v; x2]) wk (fval f).
  Proof.  move: (valP f); exact: fanpW. Qed.

  Lemma fan_last : last wk (val f) = w0.
  Proof. move: (valP f); exact: fanp_last. Qed.

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

  Definition rotateF : edge_coloring G ColorType :=
    rotate c (rev (wk::val f)) v.

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
  
  (* TO DO: could be more general too, bc will need to prove base case anyways *)
  Lemma imset_rot_del_edge (e0 e1 : {set G}) : 
    c e0 = rotateF e1 ->
    c[E(del_edges e0)] = rotateF[E(del_edges e1)].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [/=|w1 [|w2 wss] IH] d Hws.
    (* rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //.  *)
    (* move/andP: Hws => [Hw1 _].
    have He0: [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    exact: imset_swap He0 He1. *)
  Admitted.

  (* TO DO: Helper for next lemma, finish inductive step *)
  Lemma rot_first_last : c [set v; w0] = rotateF [set v; wk].
  Proof.
    rewrite -fan_last /rotateF.
    set fs := \val f.
    elim Hf: fs c=> [|w1 [|w2 wss] IH] d //=.
    - rewrite/swap_edge. case: ifP=> [/eqP -> //| H].
      by rewrite eq_refl.
    - admit.
  Admitted.

  Lemma rot_w0_prop : w0_prop rotateF [set v; wk].
  Proof.
    have +: w0_prop c [set v; w0] by exact: fan_w0_prop.
    rewrite/w0_prop.
    have Heq: c [E(del_edges [set v; w0])] = rotateF [E(del_edges [set v; wk])] 
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
    elim: fs c=> [//|w1 ws IH] d Hd.
    case: ws IH=> [|w2 wss IH] //.
    specialize (IH (swap_edge d [set v; w1] [set v; w2])).
    (* rewrite -(IH (swap_edge d [set v; w0] [set v; w1])).  *)
  Admitted.

End Rotation.

Section MaximalFan.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v w0 : G).
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
    move/c_in_edge_neigh: Hatv=> [wj] Hine Hc.
    exists wj; rewrite/is_fanmax in Hf; move: (Hf wj); rewrite/valid_fan_vertex.
    have -> : wj \in N(v) by rewrite in_opn -in_edges.
    by rewrite /absent_prop Hine Hc Hab eq_refl /= andbT negbK.
  Qed.

End MaximalFan.