From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans alternate_path.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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



