From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
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
  Implicit Type (c : edge_coloring).

  (* A proper edge coloring is an edge coloring 
    where no two adjacent edges have the same color *)
  (* Could do x in e1 instead *)
  Definition is_proper_edge_coloring c : Prop := 
    forall (e1 e2 : {set G}), 
    e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> 
    (exists x, x \in e1 /\ x \in e2) -> c e1 != c e2.

  Definition proper_edge_coloring : Type := { c | is_proper_edge_coloring c }.

  Coercion proper_to_edge_coloring
    (pc : proper_edge_coloring) : edge_coloring :=
    proj1_sig pc.

  (* the image under a coloring c of the set of edges E *)
  Definition coloring_image c (E : {set {set G}}) : {set ColorType} := c @: E.
  Local Notation "c [ E ]" := (coloring_image c E) (at level 50).

  Lemma max_colors_at_vertex c (v : G) : #|c[E{v}]| <= max_degree G.
  Proof.
    apply: (leq_trans (leq_imset_card _ _)).
    rewrite card_edge_neigh.
    rewrite /max_degree.
    exact: leq_bigmax_cond.
  Qed.

End EdgeColoring.
Notation "c [ E ]" := (coloring_image c E) (at level 50).

Section Recolor.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (e f : {set G}) (col : ColorType).

  Definition recolor_edge e col : edge_coloring G ColorType :=
    fun edge => if edge == e then col else c edge.

  Lemma recolor_eq e col : (recolor_edge e col) e = col.
  Proof. by rewrite /recolor_edge eqxx. Qed.

  Lemma recolor_neq e f col : f != e -> (recolor_edge e col) f = c f.
  Proof. by rewrite /recolor_edge => /negPf ->. Qed.

  Definition swap_edge e f : edge_coloring G ColorType :=
    fun edge => 
      if edge == e then c f
      else if edge == f then c e
      else c edge. 

  Lemma swap_im e f : 
    e \in E(G) -> 
    f \in E(G) ->
    c[E(G)] = (swap_edge e f)[E(G)].
  Proof.
    move=> He0 He1; apply/setP => col.
    apply/imsetP/imsetP; move=> [e2 He2 ->]; rewrite /swap_edge;
    exists (if e2 == e then f else if e2 == f then e else e2) => //;
    repeat case: ifP => //; repeat move=> /eqP -> //; try rewrite eq_refl //.
    - do 2 move=> _ -> //.
    - move=> _ /eqP -> //.
  Qed.

  Lemma swap_im_vertex e f (v : G) :
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

  Definition k_edge_card {k} (kc : k_edge_coloring k) :
    #|kc[E(G)]| == k :=
    proj2_sig (projT2 kc).

  (* G is k-colorable if a k-edge-coloring exists. *)
  Definition k_edge_colorable k : Prop := inhabited (k_edge_coloring k).

  (* The chromatic index chi is the smallest k such that G is k-colorable *)
  Definition is_chromatic_index chi : Prop :=
    k_edge_colorable chi /\ forall k, k < chi -> ~ k_edge_colorable k.

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

  (* injective coloring: each edge is a color *)
  Definition inj_edge_coloring : edge_coloring G {set G} :=
    fun e => e.

  (* injective coloring is a proper coloring *)
  Definition proper_inj_coloring : proper_edge_coloring G {set G}.
  Proof.
    exists inj_edge_coloring.
    move=> e1 e2 _ _ ne _.
    exact ne.
  Defined.

  Lemma inj_im : proper_inj_coloring[E(G)] = E(G). 
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
    exists {set G}, proper_inj_coloring. by rewrite inj_im.
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

(* Definition foo : sgraph -> nat.
 intros.
 specialize (chromatic_index_exists X) as H.
 destruct H. *)

(* ----  Absent Set ---- *)
Definition absent_set {G : sgraph} {ColorType: finType} 
  (v : G) (c : edge_coloring G ColorType) :=
  setD (c[E(G)]) (c[E{v}]).

Proposition exists_absent_color (G : sgraph) :
  k_edge_colorable G (max_degree G + 1) ->
  exists c : k_edge_coloring G (max_degree G + 1),
  forall v : G, absent_set v c != set0.
Proof.
  move=> [c]; exists c => v.
  rewrite -card_gt0 cardsDS; last by apply imsetS; apply sub_all_edges.
  by rewrite subn_gt0 
            (eqP (k_edge_card c)) 
            (leq_ltn_trans (max_colors_at_vertex c v)) 
            // addn1 ltnSn.
Qed.

Section Fan.
  (* ---- Fans ---- *)
  Variable (G : sgraph) (ColorType : finType).
  Implicit Types (v w : G) (e : {set G}) (f : seq G) (c : edge_coloring G ColorType).

  (* 1. For all w in the fan centered at v, w is in the neighborhood of v *)
  Definition neigh_prop v f := all (fun w => w \in N(v)) f.

  (* 2. if w0 is the first item in fan f centered at v under coloring c,
    (v, w0) is a distinct color from the rest of the edges in the graph *)
  Definition w0_prop e c := 
    [forall (h : {set G} | (h \in E(G)) && (e != h)), c e != c h].

  (* 3. for all w_i, w_{i+1} in the fan f centered at v under coloring c,
    the color of (v, w_{i+1} is absent at w_i) *)
  Definition absent_prop c e w := 
    (c e) \in (absent_set w c).

  Definition fanp v wk c f := 
    uniq (wk::f) &&
    neigh_prop v (wk::f) &&
    w0_prop [set v; (last wk f)] c &&
    path (
      fun x2 x1 => absent_prop c [set v; x2] x1
    ) wk f.

  Lemma fanp_neigh v wk c f : fanp v wk c f -> neigh_prop v (wk::f).
  Proof. by case/andP => /andP [/andP [_ ->] _] _. Qed.

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
  | w0 :: ws =>
    match ws with
    | w1::wss =>
      rotate
          (swap_edge c [set v; w0] [set v; w1])
          v ws
    | [::] => c
    end
  | [::] => c
  end.

Lemma rotate_im
  {G : sgraph} {ColorType : finType}
  (c : edge_coloring G ColorType)
  (v : G) (fs : seq G) :
  neigh_prop v fs ->
  c[E(G)] = rotate c v fs [E(G)].
Proof.
  elim: fs c => [|w0 ws IH] c //= /andP [Hw0 Hws].
  case: ws IH Hws=> [| w1 wss IH] Hws //.
  rewrite -(IH (swap_edge c [set v; w0] [set v; w1])) //.
  move/andP: Hws => [Hw1 _].
  have He0 : [set v; w0] \in E(G) by rewrite in_opn -in_edges in Hw0.
  have He1 : [set v; w1] \in E(G) by rewrite in_opn -in_edges in Hw1.
  exact: swap_im He0 He1.
Qed.

Section Rotation. 
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType) (v wk : G) (f : Fan v wk c).
  Implicit Type (w : G).

  Lemma fan_neigh : neigh_prop v (fan_nodes f).
  Proof. move: (valP f). rewrite/fan_nodes. exact: fanp_neigh. Qed.

  Lemma in_neigh w : w \in (wk::val f) -> w \in N(v).
  Proof. 
    move: fan_neigh; rewrite/neigh_prop=> /allP H. exact: H.
  Qed.

  Definition valid_fan_vertex w :=
    (w \in N(v)) && absent_prop c [set v; w] v && (w \notin wk::val f).

  Definition extendFan : seq G := 
    match [pick w in N(v) | valid_fan_vertex w] with
    | Some w => w::wk::val f
    | None => wk::val f
    end.

  Definition rotateF : edge_coloring G ColorType :=
    rotate c v (rev (wk::val f)).

  Lemma rorate_imF_vertex : c[E{v}] = rotateF[E{v}].
  Proof.
    rewrite/rotateF; set fs := (rev (wk::val f)).
    elim: fs c=> [|w0 ws IH] d //=.
    case: ws IH=> [|w1 wss IH] //.
    rewrite -(IH (swap_edge d [set v; w0] [set v; w1])) //.
    have Hv0 : v \in [set v; w0] by rewrite in_set2 eq_refl.
    have Hv1 : v \in [set v; w1] by rewrite in_set2 eq_refl.
    exact: swap_im_vertex Hv0 Hv1.
  Qed.

  Lemma rotate_imF : c[E(G)] = rotateF[E(G)].
  Proof.
     (* could use rotate_im, but would be nice to remove that
     lemma entirely and just have this one  *)
  Admitted. 

  Definition rotHelper 
    (u : G) 
    (col_wOpt : (option G * edge_coloring G ColorType)) :=
    (Some u, 
      let (wOpt, d) := col_wOpt in 
      match wOpt with
      | None => d
      | Some w => (swap_edge d [set v; u] [set v; w])
      end).

  Definition rotate2 : edge_coloring G ColorType :=
    snd (foldr rotHelper (None, c) (wk::val f)).
  
  Lemma rotate2_im : c[E(G)] = rotate2[E(G)].
  Proof.
    rewrite /rotate2. move: (wk::val f) => fs.
    elim: fs c => [|w0 ws IH] d //=.
    rewrite IH; set rot := (foldr rotHelper (None, d) ws).
    case: rot => [[w1| ] d0] //=.
  Admitted.

  Lemma rotate2_im_vert : c[E{v}] = rotate2[E{v}].
  Proof. 
    rewrite/rotate2; move: (wk::val f) => fs.
    elim: fs c => [|w0 ws IH] d //=.
    rewrite IH; set rot := (foldr rotHelper (None, d) ws).
    case: rot => [[w1| ] d0] //=.
    have Hv0 : v \in [set v; w0] by rewrite in_set2 eq_refl.
    have Hv1 : v \in [set v; w1] by rewrite in_set2 eq_refl.
    exact: swap_im_vertex Hv0 Hv1.
  Qed.

  Lemma rot_card :
    #|c[E(G)]| == #|rotateF[E(G)]|.
  Proof. by rewrite rotate_imF. Qed.

  Lemma rot_abs_edge : absent_set v c = absent_set v rotateF.
  Proof.
    by rewrite/absent_set rotate_imF rorate_imF_vertex.
  Qed.

  (* Needs to be fixed in latex, require premise c is proper *)
  (* Thought: use other rotate definition for this, then prove equivalence of the two *)
  Lemma rot_proper : 
    is_proper_edge_coloring c ->
    is_proper_edge_coloring rotateF.
  Proof.
    rewrite/is_proper_edge_coloring=> Hprop e1 e2 He1 He2 Hneq Hx.
  Admitted.

End Rotation.

Fixpoint alternates 
  {G : sgraph} {ColorType : finType} 
  (c : edge_coloring G ColorType) (ca cb : ColorType) (p : seq G) : bool := 
    match p with 
    | x::p' =>
      match p' with 
      | y::p'' => (c [set x; y] == ca) && alternates c cb ca p'
      | _ => true
      end
    | _ => true
    end.

Section AltPath.
  Variables (G : sgraph) (ColorType : finType) (c : edge_coloring G ColorType).
  Implicit Types (x y : G) (p : seq G) (ca cb : ColorType).
  
  Definition altpath ca cb x y p := 
    alternates c ca cb (x::p) && pathp x y p.

  Lemma altpathW ca cb x y p : altpath ca cb x y p -> pathp x y p.
  Proof. by case/andP. Qed.
  
  Lemma altpathWW ca cb x y p : altpath ca cb x y p -> path (--) x p.
  Proof. by move/altpathW/pathpW. Qed.

  Lemma altpathxx ca cb x : altpath ca cb x x [::].
  Proof.
    apply/andP; split => //.
  Qed.

  Lemma path_altpath {x y} ca cb (pth : Path x y) : 
    alternates c ca cb (x :: val pth) -> altpath ca cb x y (val pth).
  Proof. 
    move => Ap. apply/andP; split=> //. exact: valP pth.
  Qed.

  Lemma alternate_cons ca cb x y p :
   alternates c ca cb (x::y::p) = 
   (c [set x; y] == ca) && alternates c cb ca (y::p).
  Proof. 
  Admitted.

  Lemma altpath_cons ca cb x y z p : 
    altpath ca cb x y (z :: p) =
    [&& x -- z, c [set x; z] == ca & altpath cb ca z y p].
  Proof. 
    by rewrite /altpath alternate_cons pathp_cons andbCA -andbA.
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
  Variables (G : sgraph) (x y : G) (ColorType : finType) (ca cb : ColorType) (c : edge_coloring G ColorType).
  Implicit Type (v : G) (ap : AltPath c ca cb x y) (p : Path x y).

  Definition next_col ap : ColorType :=
    let fix next ca' cb' pth := 
      match pth with 
        | [::] => cb'
        | _::tl => next cb' ca' tl
      end in 
    next ca cb (x::val ap).

  (* singleton path *)
  Definition idap ca cb x : AltPath c ca cb x x := Build_AltPath (altpathxx c ca cb x).

  (* Convert path to altpath if path alternates ca cb *)
  Definition altpath_of p (AH : alternates c ca cb (x :: val p)) : AltPath c ca cb x y := 
    Sub (val p) (path_altpath AH).
  
  (* Definition apcons_proof := altpath_cons (valP p) (valP q). *)
  (* Definition apcons : AltPath c ca cb x y := Sub (val p ++ val q) pcat_proof. *)

  Definition next_alt_vertex v ap :=
    (v \in N(y)) && (c [set v; y] == next_col ap).

  (* Todo: concat path for Some v; recursively call extend_path *)
  (* Careful of cycles, either require that ca is in the absent
  set of the first vertex in p or update valid_alt for uniqueness*)
  Definition extend_path ap := 
    match [pick v in N(y) | next_alt_vertex v ap] with 
    | None => ap
    | Some v => ap (* add v to the AltPath *)
    end.

  Definition kempe_chain v := extend_path (idp v).

End Kempe.

Theorem Vizings (G : sgraph) : 
  is_chromatic_index chi -> 
  max_degree G <= chi && chi <= max_degree G + 1.
 
