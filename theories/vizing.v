From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux.
Require Import edge_coloring.
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

  (* Lemma none_w0_extended {k : nat} {e} (He : e \in E(G)) (kc_del : k_edge_coloring (del_edges e) k) w
  : ((k_extended_col He kc_del) [set v; w] = None) = (w = (last wk (val f))).
  Proof.
  Admitted. *)
  (* Lemma w0_none_extended 
    {k} {v w0 : G}
    {He : [set v; w0] \in E(G)}
    {kc_del : k_edge_coloring (del_edges [set v; w0]) k}
    (f : k_Fan_of_del_edges He kc_del)
    (w : G)
  : ((k_extended_col He kc_del) [set v; w] = None) = (w = (last wk (val f))).
  Proof. 
    rewrite /w0_prop /extended_col eq_refl.
    by apply/negP => /imsetP [e' /del_edges1_neq /negbTE ->].
  Qed. *)
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

  Lemma perm_rot : 
    perm_eq [seq c e | e <- enum E(G)] [seq rotateF e | e <- enum E(G)].
  Proof.
    rewrite /rotateF; set fs := (rev (wk::val f)).
    have Hws: neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws => [|w1 [|w2 wss] IH] d //= /andP [Hw1 Hws].
    apply: (perm_trans _ (IH (swap_edge d [set v; w1] [set v; w2]) _)) => //.
    move/andP: Hws => [Hw2 _].
    have He1: [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    have He2: [set v; w2] \in E(G) by rewrite in_opn -in_edges in Hw2.
    exact: perm_swap He1 He2.
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

Section AltPathOps.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (c : edge_coloring G ColorType) (ca cb : ColorType) (s : seq G).

  Fixpoint alternates c ca cb s : bool := 
    match s with 
    | x :: ((y :: tl) as s') =>
      (c [set x; y] == ca) && alternates c cb ca s'
    | _ => true
    end.

  Fixpoint next_col c ca cb s : ColorType := 
    match s with 
    | _ :: s' => next_col c cb ca s'
    | _ => cb
    end.

  Fixpoint alternates_invert c ca cb s : edge_coloring G ColorType :=
    match s with
    | x :: ((y::tl) as s') =>
        alternates_invert
            (recolor_edge c [set x; y] ca)
            cb ca s'
    | _ => c
    end.
End AltPathOps.

Section AltPath.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (x y z : G).
  Implicit Types (ca cb : ColorType) (s : seq G) (p : Path x y) (zx: z -- x) (yz: y -- z).
  
  Lemma alternates_rcons ca cb yz p : 
    alternates c ca cb (nodes (pcat p (edgep yz))) = 
    alternates c ca cb (nodes p) && (c [set y; z] == next_col c ca cb (nodes p)).
  Proof.
  Admitted.

  Lemma alternate_cons ca cb zx p :
    alternates c ca cb (nodes (pcat (edgep zx) p)) = 
    (c [set z; x] == ca) && alternates c cb ca (nodes p).
  Proof.
    rewrite nodes_pcat !nodesE.
    by case: (val p).
  Qed.

  Lemma alternates_ca_cb ca cb p :
    ((alternates c ca cb (nodes p)) && (alternates c cb ca (nodes p))) -> ((ca == cb) || (x == y)).
  Proof.
  Admitted.
    (* move: x; elim p=> [//| y p'] IH. 
    rewrite -{3}cat1s cat_nilp=> x.
    rewrite 2!alternate_cons=> /andP[/andP[/eqP Hca Hab] /andP[/eqP Hcb Hac]].
    by have ->: (ca == cb) by rewrite -Hca Hcb.
  Qed. *)

  Definition altpath ca cb {u v : G} (p0 : Path u v) := alternates c ca cb (nodes p0) && (irred p0).

  Lemma altpathE ca cb {u v : G} (p0 : Path u v) : altpath ca cb p0 = alternates c ca cb (nodes p0) && (irred p0).
  Proof. by []. Qed.

  Definition altpath_next_col {ca cb p} (ap : altpath ca cb p) : ColorType :=
    next_col c ca cb (nodes p).

  Lemma altpath_idp ca cb : altpath ca cb (idp x).
  Proof. by rewrite altpathE nodesE irred_idp. Qed.

  Lemma altpath_edge ca cb xy : (@altpath ca cb x y (edgep xy)) = (c [set x; y] == ca).
  Proof. by rewrite altpathE nodesE irred_edge /=. Qed.

  Lemma altpath_edgeL ca cb zx p : 
    altpath ca cb (pcat (edgep zx) p) = (z \notin p) && (c [set z; x] == ca) && (altpath cb ca p).
  Proof.
    case: p=> p pth_p.
    rewrite !altpathE irred_edgeL mem_path !nodesE /=.
    by rewrite !andbA (andbAC _ _ (z  \notin x :: p)) (andbC _ (z  \notin x :: p)).
  Qed.
  
  Lemma altpath_edgeR ca cb p yz :
    altpath ca cb (pcat p (edgep yz)) = (z \notin p) && (c [set y; z] == next_col c ca cb (nodes p)) && altpath ca cb p.
  Proof.
    rewrite !altpathE irred_edgeR alternates_rcons.
    (* by rewrite !andbA (andbC (alternates ca cb (nodes p)) _). (andbAC _ _ (z  \notin p)).  *)
  Admitted.

  Definition altpath_endpt {ca cb p} (ap : altpath ca cb p) (u : G) :=
    (ca \in absent_set c u) \/ (cb \in absent_set c u). 

  Lemma altpath_endptP {ca cb p} (ap : altpath ca cb p) (u : G) :
    (ca \in absent_set c u) \/ (cb \in absent_set c u) -> altpath_endpt ap u.
  Proof. by []. Qed.

  Lemma altpath_two_endpts {ca cb p} (ap : altpath ca cb p) (u v : G) :
    altpath_endpt ap z /\ altpath_endpt ap u /\ altpath_endpt ap v ->
    (z \notin p ) \/ (u \notin p) \/ (v \notin p).
  Proof.
  Admitted.

End AltPath.

Lemma altpath_mem 
  {G : sgraph} {ColorType : finType} 
  (c : edge_coloring G ColorType) 
  (ca cb : ColorType)
  (x y u v : G)
  (p : Path x y) :
  altpath c ca cb p ->
  Path_edge p u v -> 
  (c [set u; v] == ca) || (c [set u; v] == cb).
Proof.
  elim: p ca cb=> [_ _ _ /idp_path_edge //|x0 z0 p xz0 IH] ca cb.
  rewrite altpath_edgeL=> /andP[/andP[Hnin Hc0] Hap] /cat_path_edge.
  case=> [/edgep_path_edge /andP[/eqP <- /eqP <-]|He]; first by rewrite Hc0.
  by move/orP: (IH cb ca Hap He)=> [->|->].
Qed.

Section Kempe.
  Variables (G : sgraph) (ColorType : finType) (pc : proper_edge_coloring G ColorType) (ca cb : ColorType) (x : G). 
  Implicit Types (y : G).
  Hypothesis start_abs : cb \in absent_set pc x.
 
  Definition valid_altpath_vertex {y} {p : Path x y} (ap : altpath pc ca cb p) (z : G) :=
    (z \in N(y)) && ((proper_to_edge_coloring pc) [set y; z] == altpath_next_col ap).

  Lemma valid_altpath_edge 
    {y z} {p : Path x y} 
    {ap : altpath pc ca cb p}
    (Pz : valid_altpath_vertex ap z) 
  : y -- z.
  Proof. 
  Admitted.
  
  Lemma altpath_rcons 
    {y} {p : Path x y} 
    (ap : altpath pc ca cb p) 
    (z : G) 
    (Pz : valid_altpath_vertex ap z) 
  : altpath pc ca cb (pcat p (edgep (valid_altpath_edge Pz))).
  Proof.
  Admitted.
  
  Definition is_apmax {y} {p : Path x y} (ap : altpath pc ca cb p) : Prop :=
    altpath_next_col ap \in absent_set pc y.

  Equations apmax {y} {p : Path x y} (ap : altpath pc ca cb p) 
  : {z & {q : Path x z & altpath pc ca cb q}} by wf #|[set: G] :\: ([set v in p])| lt :=
    apmax ap := 
    match pickP (valid_altpath_vertex ap) with
      | Pick z Pz => apmax (altpath_rcons Pz)
      | Nopick _ => existT _ y (existT _ p ap)
    end.
  Next Obligation.
    apply/ltP/proper_card/properP.
    (* rewrite mem_pcat_edgeR.
    split.
    - apply/setDS.  *)
  Admitted.

  Lemma apmax_is_max {y} {p : Path x y} (ap : altpath pc ca cb p)
  : is_apmax (projT2 (projT2 (apmax ap))).
  Proof.
  Admitted.

  Lemma apmax_pcat {y} {p : Path x y} (ap : altpath pc ca cb p) :
    exists q, projT1 (projT2 (apmax ap)) = pcat p q.
  Proof.
  Admitted.

End Kempe.

Section Invert.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (ca cb : ColorType) (x y : G).

  Definition invert 
    {ca cb x y} 
    {p : Path x y} 
    (ap : altpath c ca cb p) 
  : edge_coloring G ColorType :=
    alternates_invert c ca cb (nodes p).

  Lemma invert_proper 
    {ca cb x y} 
    {p : Path x y} 
    (ap : altpath c ca cb p) 
  : 
    is_proper_edge_coloring c -> 
    is_proper_edge_coloring (invert ap).
  Proof.
  Admitted.

  Lemma imset_invert 
    {ca cb x y} 
    {p : Path x y} 
    (ap : altpath c ca cb p)
  : ca \in c[E(G)] -> (invert ap) [E(G)] \subset c [E(G)].
  Proof.
    rewrite/invert.
    elim: p ca cb c ap => [|u v q uv IH] ca cb d; 
    [|rewrite nodes_pcat /edgep]; 
    rewrite !nodesE // -[val (edgep uv)]/[:: v] /behead altpath_edgeL.
    (* manually rewrite, otherwise unfolds too far *)
    rewrite -[alternates_invert d ca cb ([:: u;  v] ++ \val q)]/(alternates_invert (recolor_edge d [set u; v] ca) cb ca (v::val q)).
    elim: q IH=> [/= _|w z q' wz _] IH; first by exact: imset_recolor.
    move=>/andP[/andP[Hnu tmp0] Hap]; move: (Hap). 
    rewrite -nodesE altpath_edgeL=>/andP[/andP[tmp1 /eqP Hwzb] Hap'].
    have Hcb : cb \in (recolor_edge d [set u; w] ca)[E(G)].
    {
      have Hnwz : w != z by move/sg_edgeNeq: (wz); rewrite eq_sym=> /negbT.
      have : [set w; z] != [set u; w].
      {
        apply/eqP; rewrite doubleton_eq_iff; case.
        - by move=> [_ Hwz]; rewrite Hwz eq_refl in Hnwz.
        - (* use Hnu and mem lemmas to say u != w *)
          admit.
      }  
    (* have : recolor_neq ([set w; z] != [set u; w]).  
    have : cb \in d [E(G)] by apply/imsetP; exists [set w; z]; move: (wz); rewrite //= in_edges.   *)
      admit.
    }
    move: (IH cb ca (recolor_edge d [set u; w] ca)).
  Admitted.

  Lemma card_invert 
    {ca cb x y} 
    {p : Path x y} 
    (ap : altpath c ca cb p)
  :
    ca \in c[E(G)] -> #|(invert ap) [E(G)]| <= #|c [E(G)]|.
  Proof.
  Admitted.

   (* Definition k_invert 
    {ca cb p} 
    (ap : altpath ca cb p)
    (Hpc : is_proper_edge_coloring c)
    (Hca : ca \in c[E(G)])
  : k_edge_coloring G #|c[E(G)]|.
  Proof.
    refine (existT _ ColorType (exist _ (exist _ (invert ap) (invert_proper Hpc)) _)).
    exact: card_invert Hca.
  Defined. *)
End Invert.

Section InvertProp.
  Variables (G : sgraph) (ColorType : finType) (pc : proper_edge_coloring G ColorType) (ca cb : ColorType) (x y : G) (p : Path x y) (ap : altpath pc ca cb p).
  Implicit Types (u v : G).
  Hypothesis Ha : is_apmax ap.

  Definition not_mem_inverted : Prop := 
    forall u v, ~ Path_edge p u v -> 
    (proper_to_edge_coloring pc) [set u; v] = (invert ap) [set u; v].
  
  Definition mem_inverted : Prop :=
    forall u v, Path_edge p u v ->
    (((proper_to_edge_coloring pc) [set u; v] = ca) <-> ((invert ap) [set u; v] = cb)) /\
    (((proper_to_edge_coloring pc) [set u; v] = cb) <-> ((invert ap) [set u; v] = ca)).

  Lemma invert_is_inverted : not_mem_inverted /\ mem_inverted.
  Proof.
    rewrite/not_mem_inverted/mem_inverted; split=> u v Hp.
  Admitted.

  Lemma invert_absent_not_mem {u} (Hu : u \notin p) :
    (invert ap)[E(G)] = pc[E(G)] -> absent_set pc u = absent_set (invert ap) u.
  Proof. 
    have : pc [E{G;u}] = invert ap [E{G;u}].
    {
      (* apply/setP=> c0.
      apply/imsetP/imsetP; move=> [e Hin ->]; exists e=> //.
      move: Hin; rewrite/edge_neigh=> /imsetP [v] Hn ->.
      have := vert_not_in_path.
      move: invert_is_inverted=> [Hnm _].   *)
      admit.
    }
    by rewrite/absent_set=> -> ->.
  Admitted.

  Lemma invert_absent_ca {u}
    (Hu : u \in p)
    (Habu : cb \in absent_set pc u)
  : ca \in absent_set (invert ap) u.
  Proof.
  Admitted.

  Lemma invert_absent_cb {u}
    (Hz : u \in p)
    (Habu : ca \in absent_set pc u)
  : cb \in absent_set (invert ap) u.
  Proof.
  Admitted.

  Lemma invert_fan_nodes {u v : G} (f1 : Fan pc x v u) (f2 : Fan (invert ap) x v u):
    (u :: val f1) = (u :: val f2).
  Proof.
  Admitted.

  Lemma invert_fan {u v : G} (f : Fan pc x v u) : 
    cb \in absent_set pc x -> Fan (invert ap) x v u.
  Proof.
  Admitted.

End InvertProp.

Lemma smaller_coloring
  {G : sgraph} {v w0 wj : G} {k}
  {c : k_edge_coloring G k} 
  (f : Fan c v w0 wj) (cj : projT1 c) :
  k = max_degree G + 1 + 1 ->
  cj \in (absent_set c v :&: absent_set c wj) ->
  k_edge_colorable G (max_degree G + 1).
Proof.
  move=> Hk Hcvw.
  have Hneigh : wj \in N(v) := (in_neigh (mem_head wj (val f))).
  have Hvw : [set v; wj] \in E(G).
  { by move: Hneigh; rewrite in_opn in_edges. }
  pose c' := rotateF f.
  have Hprop' : is_proper_edge_coloring c' := rot_proper (proj2_sig (k_to_proper_coloring c)).
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
  rewrite -card_rot (card_k_col c).
  have ->: k - 1 = max_degree G + 1 by rewrite Hk addn1 subn1.
  move=> Hcard''.
  by constructor; exists (projT1 c), (exist _ c'' Hprop''); rewrite Hcard''.
Qed.

Theorem Vizings (G : sgraph) (chi : nat): 
  is_chromatic_index G chi -> 
  max_degree G <= chi <= max_degree G + 1.
Proof.
  move=> Hchi; 
  rewrite chi_lower_bound //=.
  apply (chi_upper_bound_trans Hchi) => {Hchi}.
  elim/(size_ind (fun G => #|E(G)|)) : G => G IH.
  case: (set_0Vmem E(G)) => [E0|[e Ein0]].
  - (* Base case #|E(G)| = 0 *)
    exists #|E(G)|.
    split; first by exact/inj_chrom.
    by rewrite E0 cards0.
  - (* Induction *)
    have [v [w0] [Edef0 _]] := edgesP _ Ein0; rewrite {}Edef0 in Ein0; set G' := del_edges [set v; w0].
    have{}/IH [k' [[kc'] Hleqk']]: #|E(G')| < #|E(G)| by apply: proper_card; exact: del_edges_proper Ein0 _.
    have : k' <= max_degree G + 1 by apply/(leq_trans Hleqk'); rewrite leq_add2r; exact: del_edges_max_deg.
    rewrite leq_eqVlt => /orP[/eqP Heqk'| Hltk']; first last.
    - (* if k' < max_degree G + 1, then we are done *) 
      pose kc := k_extended_col Ein0 kc'.
      exists (k' + 1); by split; [|rewrite addn1].
    (* now, k' = max_degree G + 1 *)
    rewrite {}Heqk' in kc'; pose kc := k_extended_col Ein0 kc'.
    (* create a maximal fan from w0 to w *)
    pose f0 : Fan kc v w0 w0 := k_Fan_of_del_edges Ein0 kc'.
    case Hfmax : (fanmax f0) => [w fmax].
    have HfisMax : is_fanmax fmax by move: (fanmax_is_max f0); rewrite {}Hfmax /=.
    have Hleqk : max_degree G' + 1 <= max_degree G + 1 by rewrite leq_add2r; exact: del_edges_max_deg. 
    (* there exists some color c0 absent at w *)
    move: (exists_absent_color kc' Hleqk w) => [c0] Habw0'.
    have Habw0 := extended_absent Ein0 Habw0'.
    case: (boolP (Some c0 \in absent_set kc v))=> [Habv0 | Hnabv0].
    - (* if c0 is absent at v, we can replace extra color with c0 *)
      have Hcap : (Some c0 \in absent_set kc v :&: absent_set kc w) by apply/setIP/(conj Habv0 Habw0).
      by exists (max_degree G + 1); move: (smaller_coloring fmax erefl Hcap).
    (* Otherwise, we will need to create a fan and rotate *)
    move: (exists_absent_color kc (leq_addr _ (max_degree G + 1)) v) => [c1] Habv1. 
    (* There also exists an edge v--wj colored c0, where wj != w0 is in the fan *)
    have := (fanmax_present HfisMax Hnabv0 Habw0)=> [[wj] /andP[Einj /andP[/eqP Hkcj Hfanj]]].
    have Evj : v -- wj by rewrite in_edges in Einj.
    (* split fan at wj as f1 and (wj::f2) *)
    case/splitPr fsplit: (w::val fmax)/Hfanj => [f1 f2 _].
    case Hf2: f2 fsplit=> [|wi f2'] fsplit.
    - (* contradiction if f2 is empty *)
      have Hneqj0 : wj != w0.
      { 
        apply: (@contra_neq _ _ ((proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; wj]) ((proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; w0]) _ _)=> [-> //|];
        have /eqP -> : (proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; w0] == None by move/eqP: (w0_col_extended kc').
        by rewrite Hkcj.
      }
      by rewrite -(fan_last fmax) -(last_cons w w) fsplit cats1 last_rcons eq_refl in Hneqj0.
    (* so f2 is non-empty, i.e. wi != w0 *)
    have Habwi0 : Some c0 \in absent_set kc wi.
    { 
      move: fsplit. 
      by case: f1=> [|wk f1']; [rewrite cat0s|]; 
      case=> Hw Hfval; have := fanW fmax;
      rewrite Hfval /absent_prop; [rewrite Hw | rewrite -cat_rcons cat_path last_rcons];
      rewrite /path Hkcj=> /andP[_ +] //; move=> /andP[-> _]. 
    }
    rewrite -[wj :: wi :: f2']cat1s catA in fsplit.
    have fsmallest := sub_fan fsplit.
    (* Construct c0 c1 Kempe Chain starting with v--wj *)
    move/eqP: (Hkcj); rewrite -(altpath_edge kc _ c1)=> ap0.
    case Hapmax: (apmax Habv1 ap0) => [z [pth apm]].
    have Hpv : v \in pth by exact: path_begin.
    have := apmax_pcat Habv1 ap0; rewrite Hapmax /= => [[q] Hq].
    have HaisMax : is_apmax apm by move: (apmax_is_max Habv1 ap0); rewrite {}Hapmax /=. 
    have /(imset_invert apm) /eqVproper : Some c0 \in kc[E(G)] by apply/c_in_all_edge; exists [set v; wj].
    pose Hkcp : proper_edge_coloring G (projT1 kc) :=  
      (exist _ (invert apm) (@invert_proper _ _ _ _ _ _ _ _ apm (proj2_sig (k_to_proper_coloring kc)))).
    case=> Hsi; first last.
    - exists #|Hkcp [E(G)]|.
      split; first by constructor; exact (proper_to_k_coloring Hkcp).
      move/proper_card: Hsi. 
      rewrite card_k_col -[#|Hkcp [E(G)]|]/(#|invert apm [E(G)]|)=> Hsi.
      by rewrite -(leq_add2r 1); rewrite -addn1 in Hsi.
    have Hi : #|Hkcp [E(G)]| == (max_degree G  + 1 + 1) by rewrite Hsi card_k_col.
    pose Hkci : k_edge_coloring G (max_degree G + 1 + 1) := existT _ (projT1 kc) (exist _ Hkcp Hi).
    (* v is an endpint because c1 was absent here *)
    have Hcj : (invert apm) [set v; wj] = c1.
    {
      have Hp : Path_edge pth v wj by rewrite Hq; apply cat_path_edge; left; apply edgep_path_edge.
      move: (proj2 (invert_is_inverted HaisMax) v wj Hp)=> [/iffLR H _]; exact: H Hkcj.
    }
    have Hkci_fmax : Fan Hkci v w0 w := invert_fan HaisMax fmax Habv1.
    have Habv0 : Some c0 \in absent_set Hkci v := invert_absent_ca HaisMax Hpv Habv1.
    case: (boolP (wi \in pth))=> Hpwi; exists (max_degree G + 1).
    - (* wi is in the path of apm *)
      have Hpw : w \notin pth by 
        case
          (altpath_two_endpts
            (conj (altpath_endptP apm (or_intror Habv1))
            (conj (altpath_endptP apm (or_introl Habwi0))
                  (altpath_endptP apm (or_introl Habw0)))
          )); 
        [rewrite Hpv | case; [rewrite Hpwi|]].
      rewrite (invert_absent_not_mem HaisMax Hpw Hsi) in Habw0.
      have Hcap : (Some c0 \in absent_set Hkci v :&: absent_set Hkci w) by apply/setIP/(conj Habv0 Habw0).
      by have := (smaller_coloring Hkci_fmax erefl Hcap).
    - (* wi is not in the alternating path *)
      rewrite (invert_absent_not_mem HaisMax Hpwi Hsi) in Habwi0.
      rewrite {}(invert_fan_nodes HaisMax fmax Hkci_fmax) in fsplit.
      have Hkci_fsmallest : Fan Hkci v w0 wi := sub_fan fsplit.
      have Hcap : (Some c0 \in absent_set Hkci v :&: absent_set Hkci wi) by apply/setIP/(conj Habv0 Habwi0).
      by have := (smaller_coloring Hkci_fsmallest erefl Hcap).
Qed.



