From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import Setoid CMorphisms Relation_Definitions.
From GraphTheory Require Import edone preliminaries bij digraph sgraph connectivity.
Require Import aux.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EdgeColoring.
  (* ---- Edge Coloring Functional Definition ---- *)
  Variables (G : sgraph) (ColorType : finType).

  (* An edge coloring function assigns edges in E(G) to colors *)
  Definition edge_coloring : Type := {set G} -> ColorType.
  Implicit Type (c : edge_coloring) (x : G).

  (* A proper edge coloring is an edge coloring 
    where no two adjacent edges have the same color *)
  (* Could do x in e1 instead *)
  
  Definition is_proper_edge_coloring c : Prop := 
    forall (x : G),
    {in E{x}&, forall (e1 e2 : {set G}), c e1 = c e2 -> e1 = e2}.

  Definition proper_edge_coloring : Type := { c | is_proper_edge_coloring c }.
  Implicit Type (pc : proper_edge_coloring).

  Coercion proper_to_edge_coloring
    pc : edge_coloring := proj1_sig pc.

  (* the image under a coloring c of the set of edges E *)
  Definition coloring_image c (E : {set {set G}}) : {set ColorType} := c @: E.
  Local Notation "c [ E ]" := (coloring_image c E) (at level 50).

  Lemma leq_col_deg c x : #|c[E{x}]| <= max_degree G.
  Proof. 
    apply: (leq_trans (leq_imset_card _ _)).
    rewrite card_edge_neigh.
    rewrite /max_degree.
    exact: leq_bigmax_cond.
  Qed.

  (* injective, at a vertex *)
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
    rewrite /max_degree. 
    have <- : \max_(x in G) #|E{x}| = \max_(x in G) #|N(x)|.
    { apply: bigmax_eq_pointwise => v _; by rewrite card_edge_neigh. }
    apply/bigmax_leqP=> x _. 
    apply: (leq_trans _ (leq_vertex_graph pc x)).
    by rewrite (eq_deg_pcol pc x).
  Qed.

End EdgeColoring.
Notation "c [ E ]" := (coloring_image c E) (at level 50).

Section Recolor.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (e f : {set G}) (col : ColorType).

  Definition recolor_edge e c0 : edge_coloring G ColorType :=
    fun edge => if edge == e then c0 else c edge.

  Lemma recolor_eq e c0 : (recolor_edge e c0) e = c0.
  Proof. by rewrite /recolor_edge eqxx. Qed.

  Lemma recolor_neq e f c0 : f != e -> (recolor_edge e c0) f = c f.
  Proof. by rewrite /recolor_edge => /negPf ->. Qed.

  Lemma imset_recolor e c0 : 
    c[E(del_edges e)] = recolor_edge e c0 [E(del_edges e)].
  Proof.
    apply/setP => c1.
    by apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /recolor_edge;
    exists e2 => //; case: ifP => /eqP Heq //;
    rewrite Heq in He2; move: (del_edgesN e); rewrite -in_setC => /setCP.
  Qed.

  (* not needed right now *)
  Lemma del_edges_col c0 e : 
    (c0 \in c[E(G)]) ->
    (c0 != c e) ->
    (c0 \in c[E(del_edges e)]).
  Proof.
  Admitted.

  Lemma replace_col c0 e : 
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

  Lemma imset_swap e f : 
    e \in E(G) -> 
    f \in E(G) ->
    c[E(G)] = (swap_edge e f)[E(G)].
  Proof.
    move=> He0 He1; apply/setP => c0.
    apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /swap_edge;
    exists (if e2 == e then f else if e2 == f then e else e2) => //;
    repeat case: ifP => //; repeat move=> /eqP -> //; try rewrite eq_refl //.
    - do 2 move=> _ -> //.
    - move=> _ /eqP -> //.
  Qed.

  (* TODO: finish this proof, presumably not too difficult *)
  Lemma imset_swap_vertex e f (v : G) :
    v \in e -> v \in f -> c[E{v}] = (swap_edge e f)[E{v}].
  Proof.
  Admitted.

End Recolor.

Section ChromIdx.
  (* ---- Chromatic Index ---- *)
  Variables (G : sgraph).
  Implicit Types (k chi : nat).
  
  (* A k-edge-coloring is a proper coloring which uses exactly k colors *)
  Definition k_edge_coloring k : Type := 
    { ColorType : finType &
      { c : proper_edge_coloring G ColorType | #|c[E(G)]| == k } }.

  Coercion k_to_proper_coloring {k} (kc : k_edge_coloring k) : 
    proper_edge_coloring G (projT1 kc) :=
    proj1_sig (projT2 kc).

  Definition card_k_col {k} (kc : k_edge_coloring k) :
    #|kc[E(G)]| == k :=
    proj2_sig (projT2 kc).

  (* G is k-colorable if a k-edge-coloring exists. *)
  Definition k_edge_colorable k : Prop := inhabited (k_edge_coloring k).

  (* The chromatic index chi is the smallest k such that G is k-colorable *)
  Definition is_chromatic_index chi : Prop :=
    k_edge_colorable chi /\ forall k, k < chi -> ~ k_edge_colorable k.

  (* We can already lower bound the chromatic index *)
  Theorem lower_bound (chi : nat): 
    is_chromatic_index chi -> 
    max_degree G <= chi.
  Proof. 
    do 3![elim] => ColorType H _. 
    elim: H=> c /eqP <-.
    by rewrite leq_maxdeg_pcol.
  Qed.

  (*  Any valid k-edge-colorable upper bounds chi *)
  Lemma chromatic_index_upper_bound k chi :
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

  (* ----  One-to-one Coloring ---- *)

  (* Todo: can we use Program Definition, is this better? Should we do this elsewhere too? *)
  Program Definition in_edge_coloring2 : proper_edge_coloring G {set G} := 
    fun e => e.
  Next Obligation. by move=> _ e1 e2 _ _ eq. Qed. 

  (* injective coloring: each edge is a color *)
  Definition inj_edge_coloring : edge_coloring G {set G} :=
    fun e => e.

  (* injective coloring is a proper coloring *)
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

  (* injective coloring is a k-edge-coloring with k = #|E(G)| *)
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
  Corollary chromatic_index_le_edges (chi : nat) :
    is_chromatic_index chi -> chi <= #|E(G)|.
  Proof.
    move=> Hchi. 
    apply (chromatic_index_upper_bound Hchi inj_chrom).
  Qed.

  (* make ab set, not straigth existsnec. sig.  *)
  Lemma chromatic_index_exists : exists chi, is_chromatic_index chi.
  Proof.
  have Hbase: k_edge_colorable #|E(G)| by exact: inj_chrom.
  (* Use well-ordering to find minimum *)
  Admitted.

  (* Todo: Lemma chromatic_index_unique *)
  (*Definition tmp : nat.
    destruct chromatic_index_exists as [n foo].
    Check chromatic_index_exists.
  *)
End ChromIdx.

Section AbsentSet.
  Variables (G : sgraph).
  Implicit Types (x y : G).

  Definition absent_set {ColorType: finType} 
    (c : edge_coloring G ColorType) x :=
    setD (c[E(G)]) (c[E{x}]).

  (* still deciding on definitions further down, tbd which of these three will be needed *)
    Lemma absent_col {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x :
    c0 \in absent_set c x <-> [pick e in E{x} | c e == c0] == None.
  Proof. split=> H. Admitted.

  Lemma absent_edge_col {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x y :
    c0 \in absent_set c x -> y \in N(x) -> c0 != c [set x; y].
  Proof. Admitted.

  Lemma absent_present {ColorType: finType} (c : edge_coloring G ColorType) (c0 : ColorType) x y :
    c0 \in c[E(G)] -> c0 \in absent_set c x -> y \in N(x) -> c0 \in c[E(del_edges [set x; y])].
  Proof. Admitted.

  Proposition exists_absent_color :
    k_edge_colorable G (max_degree G + 1) ->
    exists c : k_edge_coloring G (max_degree G + 1),
    forall x : G, absent_set c x != set0.
  Proof.
    move=> [c]; exists c => x.
    rewrite -card_gt0 cardsDS; last by apply imsetS; apply sub_all_edges.
    by rewrite subn_gt0 
              (eqP (card_k_col c)) 
              (leq_ltn_trans (leq_col_deg c x)) 
              // addn1 ltnSn.
  Qed.
  
End AbsentSet.

Section Fan.
  Variable (G : sgraph) (ColorType : finType).
  Implicit Types (v w : G) (e : {set G}) (f : seq G) (c : edge_coloring G ColorType).

  (* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
  Definition neigh_prop v f := all (fun w => w \in N(v)) f.

  (* 2. if w0 is the first item in fan f centered at v under coloring c,
    (v, w0) is a distinct color from the rest of the edges in the graph *)
  (* Todo: two equivalent definitions, choose one *)
  Definition w0_prop1 c e := c e \notin c[E(del_edges e)].
    
  Definition w0_prop2 c e := 
    [forall (h : {set G} | (h \in E(G)) && (e != h)), c e != c h].

  (* Todo: decide which w0_prop to use, they are equivalent *)
    Lemma w0_props c e : reflect (w0_prop1 c e) (w0_prop2 c e).
  Proof. 
  Admitted.

    (* 3. for all w_i, w_{i+1} in the fan f centered at v under coloring c,
    the color of (v, w_{i+1} is absent at w_i) *)
  Definition absent_prop c e w := 
    (c e) \in (absent_set c w).

  Definition fanp v wk c f := 
    uniq (wk::f) &&
    neigh_prop v (wk::f) &&
    w0_prop2 c [set v; (last wk f)] &&
    path (
      fun x2 => absent_prop c [set v; x2]
    ) wk f.

  Lemma fanp_neigh v wk c f : fanp v wk c f -> neigh_prop v (wk::f).
  Proof. by case/andP => /andP [/andP [_ ->] _] _. Qed.

  Lemma rev_neigh v wk f : neigh_prop v (wk::f) -> neigh_prop v (rev (wk::f)).
  Proof. by rewrite /neigh_prop all_rev. Qed.

  Lemma fan_cons {v wk c f} w (fan : fanp v wk c f) : 
    w \in N(v) ->
    w \notin (wk::f) -> 
    absent_prop c [set v; w] wk ->
    fanp v w c (wk::f).
  Proof. 
    move: fan.
    by rewrite /fanp last_cons /neigh_prop => /andP[/andP[/andP[Hu Hn]] -> Hp] Hin Hnin Ha.
    (* rewrite cons_uniq {}Hnin {}Hu.
    rewrite -cat1s all_cat all_seq1.
    by rewrite -cat1s cat_path. *)
  Qed.

End Fan.

Section Pack.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (v w : G) (c : edge_coloring G ColorType).

  Section FanDef.
    Variables (v w : G) (c : edge_coloring G ColorType).

    Record Fan : predArgType := { fval : seq G; _ : fanp v w c fval }.

    HB.instance Definition _ := [isSub for fval].
    HB.instance Definition _ := [Countable of Fan by <:].

  End FanDef.
End Pack.

Definition fan_nodes 
  (G : sgraph) (ColorType : finType) (v wk : G) (c : edge_coloring G ColorType) (f : Fan v wk c) 
  := wk :: val f.

(* Definition in_fan_nodes 
  (G : sgraph) (ColorType : finType) (v wk : G) (c : edge_coloring G ColorType) (f : Fan v wk c) 
  : collective_pred G := 
  [pred u | u \in fan_nodes f].
Canonical Fan_predType 
  (G : sgraph) (ColorType : finType) (v wk : G) (c : edge_coloring G ColorType) (f : Fan v wk c)  
  := Eval hnf in @PredType G 
      (Fan v wk c) (@in_fan_nodes G ColorType v wk c).
Coercion in_fan_nodes : Fan >-> collective_pred. *)

(* Could update this to take in an actual fan, then don't need first match
  case because fans always have at least one element, but would need to prove this.
  this allows us to be more general at least. *)
Fixpoint rotate
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (v : G)
  (fs : seq G)
  : edge_coloring G ColorType :=
  match fs with
  | w0 :: ((w1::tl) as ws) =>
      rotate
          (swap_edge c [set v; w0] [set v; w1])
          v ws
  | _ => c
  end. 

Section Rotation. 
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v wk : G) (f : Fan v wk c).
  Implicit Type (w : G).

  Lemma fan_neigh : neigh_prop v (fan_nodes f).
  Proof. move: (valP f). rewrite/fan_nodes. exact: fanp_neigh. Qed.

  Lemma in_neigh w : w \in (wk::val f) -> w \in N(v).
  Proof. 
    move: fan_neigh; rewrite/neigh_prop=> /allP H. exact: H.
  Qed.

  Definition fancons {w}
    (Hin : w \in N(v))
    (Hnin: w \notin wk::val f)
    (Hab : absent_prop c [set v; w] wk) 
  := Build_Fan (fan_cons (valP f) Hin Hnin Hab).

  Definition valid_fan_vertex w :=
    (w \in N(v)) && (w \notin wk::val f) && absent_prop c [set v; w] wk.

  Definition extend_fan : option {w & Fan v w c} := 
    match pickP (valid_fan_vertex) with
    | Pick w Pw => 
      let Hins := (andP Pw).1 in
        let Hin := (andP Hins).1 in
        let Hnin := (andP Hins).2 in
      let Hab := (andP Pw).2 in
      Some (existT _ w (fancons Hin Hnin Hab)) 
    | Nopick _ => None
    end.

  Definition rotateF : edge_coloring G ColorType :=
    rotate c v (rev (wk::val f)).

  Lemma imset_rot_vertex : c[E{v}] = rotateF[E{v}].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    elim: fs c=> [|w0 ws IH] d //=.
    case: ws IH=> [|w1 wss IH] //.
    rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //.
    have Hv0 : v \in [set v; w0] by rewrite in_set2 eq_refl.
    have Hv1 : v \in [set v; w1] by rewrite in_set2 eq_refl.
    exact: imset_swap_vertex Hv0 Hv1.
  Qed.

  Lemma imset_rot : c[E(G)] = rotateF[E(G)].
  Proof.
    rewrite /rotateF; set fs := (rev (wk::val f)).
    have Hws : neigh_prop v fs by apply rev_neigh; exact: fan_neigh.
    elim: fs c Hws=> [|w0 ws IH] d //= /andP [Hw0 Hws].
    case: ws IH Hws=> [|w1 wss IH] Hws //.
    rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //. 
    move/andP: Hws => [Hw1 _].
    have He0 : [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
    have He1 : [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
    exact: imset_swap He0 He1.
  Qed.

  Lemma card_rot :
    #|c[E(G)]| = #|rotateF[E(G)]|.
  Proof. by rewrite imset_rot. Qed.

  Lemma rot_abs_edge : absent_set c v = absent_set rotateF v.
  Proof.
    by rewrite/absent_set imset_rot imset_rot_vertex.
  Qed.

  (* TODO! *)
  (* Needs to be fixed in latex, require premise c is proper *)
  (* Thought: use other rotate definition for this, then prove equivalence of the two *)
  Lemma rot_proper : 
    is_proper_edge_coloring c ->
    is_proper_edge_coloring rotateF.
  Proof.
    rewrite/is_proper_edge_coloring=> Hprop x e1 e2 He1 He2 Heq.
  Admitted.

End Rotation.

Fixpoint fanmax 
  {G : sgraph} 
  {ColorType : finType} 
  {v wk : G} 
  {c : edge_coloring G ColorType} 
  (d : nat) 
  (f : Fan v wk c) 
: {w & Fan v w c} :=
    match d with 
    | 0 => existT _ wk f
    | S d' => 
      match extend_fan f with
      | Some (existT w f') => fanmax d' f'
      | None => existT _ wk f
      end
    end.

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
  Implicit Types (x y : G) (p : seq G) (ca cb : ColorType).

  Definition altpath ca cb x y p := 
    (alternates c ca cb (x::p) || alternates c cb ca (x::p)) && pathp x y p.

  Lemma altpathW ca cb x y p : altpath ca cb x y p -> pathp x y p.
  Proof. by case/andP. Qed.
  
  Lemma altpathWW ca cb x y p : altpath ca cb x y p -> path (--) x p.
  Proof. by move/altpathW/pathpW. Qed.

  Lemma altpathxx ca cb x : altpath ca cb x x [ ::].
  Proof.
    apply/andP; split => //.
  Qed.

  Lemma path_altpath {x y} ca cb (pth : Path x y) : 
    alternates c ca cb (x :: val pth) || alternates c cb ca (x :: val pth) 
    -> altpath ca cb x y (val pth).
  Proof. 
    move => Ap. apply/andP; split=> //. exact: valP pth.
  Qed.

  Definition next_col {ca cb x y p} (ap : altpath ca cb x y p) :=
    if alternates c ca cb (x :: p) then cb else ca.

  (* Not needed right now *)
  Lemma alternate_cons ca cb x y p :
   alternates c ca cb (x::y::p) = 
   (c [set x; y] == ca) && alternates c cb ca (y::p).
  Proof. 
  Admitted.

  (* Lemma altpath_cons ca cb x y z p : 
    altpath ca cb x y (z :: p) =
    [&& x -- z, c [set x; z] == ca & altpath cb ca z y p].
  Proof. 
    by rewrite /altpath alternate_cons pathp_cons andbCA -andbA.
  Qed. *)

  Lemma altpath_cons {ca cb y z p} x (ap : altpath ca cb y z p) : 
    x -- y ->
    c [set x; y] == next_col ap ->
    altpath ca cb x z (y :: p).
  Proof. 
    move: ap;
    by rewrite /altpath pathp_cons 2!alternate_cons /next_col=> /andP[/orP[->|->] ->] -> Hc;
    first rewrite Hc; last case: ifP Hc=> _ ->.
  Qed.

End AltPath. 

Section Pack.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types x y : G.
  
  Section AltPathDef.
    Variables (c : edge_coloring G ColorType) (ca cb : ColorType) (x y : G).
  
    Record AltPath : predArgType := { aval : seq G; avalP : altpath c ca cb x y aval }.
  
    HB.instance Definition _ := [isSub for aval].
    HB.instance Definition _ := [Countable of AltPath by <:].
  
  End AltPathDef.
End Pack.

Section Kempe.
  Variables (G : sgraph) (ColorType : finType) (ca cb : ColorType).
  Implicit Types (x y z : G) (c : edge_coloring G ColorType) (pc : proper_edge_coloring G ColorType).
  
  (* singleton path *)
  Definition idap c x : AltPath c ca cb x x := Build_AltPath (altpathxx c ca cb x).

  (* Convert from path to altpath *)
  (* Definition apath_of {x y} (p : Path x y) (AH : alternates c ca cb (x :: val p)) : AltPath c ca cb x y := 
    Sub (val p) (path_altpath AH). *)

  Definition apcons {c x y z} 
    (ap : AltPath c ca cb y z) 
    (xy : x -- y) 
    (Hc : c [set x; y] == next_col (valP ap)) 
  := Build_AltPath (altpath_cons xy Hc).

  Definition extend_ap {c x y} (ap : AltPath c ca cb x y) : option {w & AltPath c ca cb w y} := 
    match pickP (fun v => (v \in N(x)) && (c [set v; x] == next_col (valP ap))) with
    | Pick v Pv =>
        let Hv := prev_edge_proof (eq_rect (v \in N(x)) is_true (andP Pv).1 (x -- v) (in_opn v x)) in
        let Hc := (andP Pv).2 in
        Some (existT _ v (apcons Hv Hc))
    | Nopick _ => None
    end.
  
  (* Not needed right now *)
  Lemma extend_ap_none {c x y} (ap : AltPath c ca cb x y) : 
    extend_ap ap == None -> next_col (valP ap) \in absent_set c x.
  Proof. 
    rewrite /extend_ap; case pickP=> H _ //. 
    apply Nopick in H.
  Admitted.

  (* must be proper coloring and absent at start so no cycles when extended *)
  Definition apstart pc x y :=     
    { ap : AltPath pc ca cb x y | cb \in absent_set pc y}.

  Coercion apstart_to_altpath {pc x y} (aps : apstart pc x y) : 
    AltPath pc ca cb x y := projT1 aps.

  (* relflect= decidable propisition *)
  (* prove assumptions/invariants at each step *)
  (* number of edges left in the graph is decreasing *)
  (* upper bound the number of steps *)
  (* Get definition and then prove things about it *)

  (* the first parameter `d` is a "fuel" argument, because functions in Coq
   must be guaranteed to terminate. *)
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

  Definition apswap (ap : AltPath c ca cb y z) :=  *)

End Kempe.

(* Todo: finish up, nearly there. last little admits Hnotin' and Hprop'' may take a second *)
Proposition smaller_coloring 
  {G : sgraph} {ColorType : finType} {v wj : G}
  (c : proper_edge_coloring G ColorType) 
  (f : Fan v wj c) :
  #|c[E(G)]| = max_degree G + 2 ->
  (exists cj, (cj \in c[E(G)]) && (cj \in (absent_set c v :&: absent_set c wj))) ->
  k_edge_colorable G (max_degree G + 1).
Proof.
  move=> Hcard [cj] /andP[Hin].
  rewrite in_setI=> /andP[Hcv Hcw].
  have Hneigh : wj \in N(v) := (in_neigh (mem_head wj (val f))).
  have Hvw : [set v; wj] \in E(G).
  { by move: Hneigh; rewrite in_opn in_edges. }
  pose c' := rotateF f.
  have Hprop' : is_proper_edge_coloring c' := rot_proper (proj2_sig c).
  have Hin' : cj \in c'[E(del_edges [set v; wj])].
  { 
    move: (Hin) (Hcv); 
    rewrite /absent_set (imset_rot f) (imset_rot_vertex f) => Hin' Hab.
    exact: absent_present Hin' Hab Hneigh. 
  }
  have Hnotin' : c' [set v; wj] \notin c'[E(del_edges [set v; wj])] by admit.
  pose c'' := recolor_edge c' [set v; wj] cj.
  have Hprop'' : is_proper_edge_coloring c'' by admit.
  constructor.
  move: (replace_col Hvw Hin' Hnotin'); 
  rewrite -card_rot Hcard addn2 subn1 /= -addn1=> Hcard''.
Admitted.

(* TODO *)
Theorem Vizings (G : sgraph) (chi : nat): 
  is_chromatic_index G chi -> 
  max_degree G <= chi <= max_degree G + 1.
Proof.
  move=> Hchi. rewrite lower_bound //=. move: Hchi.
  (* see edges_sum_degrees proof *)
  elim/(size_ind (fun G => #|E(G)|)) : G chi => G IH chi.
  case: (set_0Vmem E(G)) => [E0|[e edge_e]].
  - move/chromatic_index_le_edges => He.
    by apply/(leq_trans He); rewrite E0 cards0.
  - have [x [y] [def_e xy]] := edgesP _ edge_e; set G' := del_edges e.
    have/IH E' : #|E(G')| < #|E(G)|.
    { by apply: proper_card; exact: del_edges_proper edge_e _. }
Admitted.


 
