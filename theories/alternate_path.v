From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AltPathOps.
  Variables (G : sgraph) (ColorType : finType).
  Implicit Types (c : edgeColoringType G ColorType) (ca cb : ColorType) (s : seq G).

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

  Fixpoint alternates_invert c ca cb s : edgeColoringType G ColorType :=
    match s with
    | x :: ((y::tl) as s') =>
        alternates_invert
            (recolor_edge c [set x; y] ca)
            cb ca s'
    | _ => c
    end.
End AltPathOps.
  
Section AltPath.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (x y z : G).
  Implicit Types (ca cb : ColorType) (s : seq G) (p : Path x y) (zx: z -- x) (yz: y -- z).
  
  Lemma alternates_rcons ca cb yz p : 
    alternates c ca cb (nodes (pcat p (edgep yz))) = 
    alternates c ca cb (nodes p) && (c [set y; z] == next_col c ca cb (nodes p)).
  Proof.
    elim: p yz.
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
    by rewrite !altpathE irred_edgeR alternates_rcons !andbA (andbC (alternates c ca cb (nodes p)) _) (andbAC _ _ (z  \notin p)) (andbC _ (z  \notin p)).
  Qed.

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
  (c : edgeColoringType G ColorType) 
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
  
Section AltMax.
  Variables (G : sgraph) (ColorType : finType) (pc : properEdgeColoringType G ColorType) (ca cb : ColorType) (x : G). 
  Implicit Types (y : G).
  Hypothesis start_abs : cb \in absent_set pc x.
  
  Definition valid_altpath_vertex {y} {p : Path x y} (ap : altpath pc ca cb p) (z : G) :=
    (z \in N(y)) && ((proper_to_edge_coloring pc) [set y; z] == altpath_next_col ap).

  Lemma valid_altpath_edge 
    {y z} {p : Path x y} 
    {ap : altpath pc ca cb p}
  : valid_altpath_vertex ap z -> y -- z.
  Proof. 
    by rewrite/valid_altpath_vertex in_opn=> /andP[-> _].
  Qed.
  
  Lemma altpath_rcons 
    {y} {p : Path x y} 
    (ap : altpath pc ca cb p) 
    (z : G) 
    (Pz : valid_altpath_vertex ap z) 
  : altpath pc ca cb (pcat p (edgep (valid_altpath_edge Pz))).
  Proof.
    rewrite altpath_edgeR. move: Pz=> /andP[Hn Hc].
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

End AltMax.

Section Invert.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType).
  Implicit Types (ca cb : ColorType) (x y : G).

  Definition invert 
    {ca cb x y} 
    {p : Path x y} 
    (ap : altpath c ca cb p) 
  : edgeColoringType G ColorType :=
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

End Invert.

Section InvertProp.
  Variables (G : sgraph) (ColorType : finType) (pc : properEdgeColoringType G ColorType) (ca cb : ColorType) (x y : G) (p : Path x y) (ap : altpath pc ca cb p).
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
      apply/setP=> c0.
      apply/imsetP/imsetP; move=> [e Hin ->]; exists e=> //;
      move: Hin; rewrite/edge_neigh=> /imsetP [v] Hn ->;
      have Hp := (vert_not_in_path (or_introl Hu));
      move: invert_is_inverted=> [+ _];
      rewrite/not_mem_inverted=> Hnm;
      by have := Hnm u v (Hp v).  
    }
    by rewrite/absent_set=> -> ->.
  Qed.

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