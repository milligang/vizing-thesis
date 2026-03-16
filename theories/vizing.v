From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans alternate_path kempe.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma smaller_coloring
  {G : sgraph} {v w0 wj : G} {k}
  {c : kEdgeColoringType G k} 
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

Lemma base_case (G : sgraph) (no_edges : E(G) = set0) :
  k_edge_colorable G 0 /\ 0 <= max_degree G + 1.
Proof.
  split; last by []. 
  move/eqP: no_edges; rewrite -cards_eq0=> /eqP <-.
  exact/inj_chrom.
Qed.

Theorem Vizings_altpath (G : sgraph) (chi : nat): 
  is_chromatic_index G chi -> 
  max_degree G <= chi <= max_degree G + 1.
Proof.
  move=> is_chi; 
  rewrite chi_lower_bound //=.
  apply (chi_upper_bound_trans is_chi)=> {is_chi} {chi}.
  (* Induction on # of edges *)
  elim/(size_ind (fun G => #|E(G)|)) : G=> G IH.
  case: (set_0Vmem E(G))=> [/base_case|[e Ein0]]; first by exists 0.
  have [v [w0] [Edef0 _]] := edgesP _ Ein0; rewrite {}Edef0 in Ein0; set G' := del_edges [set v; w0].
  have leq_gg': max_degree G' + 1 <= max_degree G + 1 by rewrite leq_add2r; exact: del_edges_max_deg. 
  have{}/IH [k' [[kc'] leq_kg']] : #|E(G')| < #|E(G)| by apply: proper_card; exact: del_edges_proper Ein0 _.
  have: k' <= max_degree G + 1 by exact: (leq_trans leq_kg' leq_gg').
  rewrite leq_eqVlt=> /orP[/eqP eq_kg|] {leq_kg'}; first last.
  - (* if k' < max_degree G + 1, then we are done *) 
    pose kc := k_extended_col Ein0 kc'.
    exists (k' + 1); by split; [|rewrite addn1].
  (* now, k' = max_degree G + 1 *)
  rewrite {}eq_kg in kc'; pose kc := k_extended_col Ein0 kc'.
  (* create a maximal fan from w0 to w *)
  pose f0: Fan kc v w0 w0 := k_Fan_of_del_edges Ein0 kc'.
  case Hfmax: (fanmax f0) => [w fmax].
  have is_fmax: is_fanmax fmax by move: (fanmax_is_max f0); rewrite {}Hfmax /=.
  (* there exists some color c0 absent at w *)
  move: (exists_absent_color kc' leq_gg' w)=> [c0] Habw0' {leq_gg'}.
  have{Habw0'} Habw0 := extended_absent Ein0 Habw0'.
  case: (boolP (Some c0 \in absent_set kc v))=> [Habv0 | Hnabv0].
  - (* if c0 is absent at v, we can replace extra color with c0 *)
    have Hcap: (Some c0 \in absent_set kc v :&: absent_set kc w) by apply/setIP/(conj Habv0 Habw0).
    by exists (max_degree G + 1); move: (smaller_coloring fmax erefl Hcap).
  (* Otherwise, we will need to create a fan and rotate *)
  move: (exists_absent_color kc (leq_addr _ (max_degree G + 1)) v) => [c1] Habv1. 
  (* There also exists an edge v--wj colored c0, where wj != w0 is in the fan *)
  have := (fanmax_present is_fmax Hnabv0 Habw0)=> [[wj] /andP[Einj /andP[/eqP Hkcj Hfanj]]] {is_fmax Hnabv0}.
  have Evj : v -- wj by rewrite in_edges in Einj.
  (* split fan at wj as f1 and (wj::f2) *)
  case/splitPr fsplit: (w::val fmax)/Hfanj => [f1 f2 _].
  case: f2 fsplit=> [|wi f2'] fsplit.
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
  have /(imset_invert apm) /eqVproper : Some c0 \in kc[E(G)] by apply/in_c_all_edgeP; exists [set v; wj].
  pose Hkcp : properEdgeColoringType G (projT1 kc) :=  
    (exist _ (invert apm) (@invert_proper _ _ _ _ _ _ _ _ apm (proj2_sig (k_to_proper_coloring kc)))).
  case=> Hsi; first last.
  - exists #|Hkcp [E(G)]|.
    split; first by constructor; exact (proper_to_k_coloring Hkcp).
    move/proper_card: Hsi. 
    rewrite card_k_col -[#|Hkcp [E(G)]|]/(#|invert apm [E(G)]|)=> Hsi.
    by rewrite -(leq_add2r 1); rewrite -addn1 in Hsi.
  have card_ic : #|Hkcp [E(G)]| == (max_degree G  + 1 + 1) by rewrite Hsi card_k_col.
  pose ikc : kEdgeColoringType G (max_degree G + 1 + 1) := existT _ (projT1 kc) (exist _ Hkcp card_ic).
  (* v is an endpint because c1 was absent here *)
  have Hcj : (invert apm) [set v; wj] = c1.
  {
    have Hp : Path_edge pth v wj by rewrite Hq; apply cat_path_edge; left; apply edgep_path_edge.
    move: (proj2 (invert_is_inverted HaisMax) v wj Hp)=> [/iffLR H _]; exact: H Hkcj.
  }
  have Hkci_fmax : Fan ikc v w0 w := invert_fan HaisMax fmax Habv1.
  have Habv0 : Some c0 \in absent_set ikc v := invert_absent_ca HaisMax Hpv Habv1.
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
    have Hcap : (Some c0 \in absent_set ikc v :&: absent_set ikc w) by apply/setIP/(conj Habv0 Habw0).
    by have := (smaller_coloring Hkci_fmax erefl Hcap).
  - (* wi is not in the alternating path *)
    rewrite (invert_absent_not_mem HaisMax Hpwi Hsi) in Habwi0.
    rewrite {}(invert_fan_nodes HaisMax fmax Hkci_fmax) in fsplit.
    have Hkci_fsmallest : Fan ikc v w0 wi := sub_fan fsplit.
    have Hcap : (Some c0 \in absent_set ikc v :&: absent_set ikc wi) by apply/setIP/(conj Habv0 Habwi0).
    by have := (smaller_coloring Hkci_fsmallest erefl Hcap).
Qed.

Theorem Vizings_kempe (G : sgraph) (chi : nat): 
  is_chromatic_index G chi -> 
  max_degree G <= chi <= max_degree G + 1.
Proof.
  move=> is_chi; 
  rewrite chi_lower_bound //=.
  apply (chi_upper_bound_trans is_chi)=> {is_chi} {chi}.
  (* Induction on # of edges *)
  elim/(size_ind (fun G => #|E(G)|)) : G=> G IH.
  case: (set_0Vmem E(G))=> [/base_case|[e Ein0]]; first by exists 0.
  have [v [w0] [Edef0 _]] := edgesP _ Ein0; rewrite {}Edef0 in Ein0; set G' := del_edges [set v; w0].
  have leq_gg': max_degree G' + 1 <= max_degree G + 1 by rewrite leq_add2r; exact: del_edges_max_deg. 
  have{}/IH [k' [[kc'] leq_kg']] : #|E(G')| < #|E(G)| by apply: proper_card; exact: del_edges_proper Ein0 _.
  have: k' <= max_degree G + 1 by exact: (leq_trans leq_kg' leq_gg').
  rewrite leq_eqVlt=> /orP[/eqP eq_kg|] {leq_kg'}; first last.
  - (* if k' < max_degree G + 1, then we are done *) 
    pose kc := k_extended_col Ein0 kc'.
    exists (k' + 1); by split; [|rewrite addn1].
  (* now, k' = max_degree G + 1 *)
  rewrite {}eq_kg in kc'; pose kc := k_extended_col Ein0 kc'.
  (* create a maximal fan from w0 to w *)
  pose f0: Fan kc v w0 w0 := k_Fan_of_del_edges Ein0 kc'.
  case Hfmax: (fanmax f0) => [w fmax].
  have is_fmax: is_fanmax fmax by move: (fanmax_is_max f0); rewrite {}Hfmax /=.
  (* there exists some color ck absent at w *)
  move: (exists_absent_color kc' leq_gg' w)=> [ck] Habw0' {leq_gg'}.
  have{Habw0'} Habw0 := extended_absent Ein0 Habw0'.
  case: (boolP (Some ck \in absent_set kc v))=> [Habv0 | Hnabv0].
  - (* if ck is absent at v, we can replace extra color with ck *)
    have Hcap: (Some ck \in absent_set kc v :&: absent_set kc w) by apply/setIP/(conj Habv0 Habw0).
    by exists (max_degree G + 1); move: (smaller_coloring fmax erefl Hcap).
  (* Otherwise, we will need to create a fan and rotate *)
  move: (exists_absent_color kc (leq_addr _ (max_degree G + 1)) v) => [cv] Habv1. 
  (* There also exists an edge v--wj colored ck, where wj != w0 is in the fan *)
  have := (fanmax_present is_fmax Hnabv0 Habw0)=> [[wj] /andP[Einj /andP[/eqP Hkcj Hfanj]]] {is_fmax Hnabv0}.
  have Evj : v -- wj by rewrite in_edges in Einj.
  (* split fan at wj as f1 and (wj::f2) *)
  case/splitPr fsplit: (w::val fmax)/Hfanj => [f1 f2 _].
  case: f2 fsplit=> [|wi f2'] fsplit.
  - (* contradiction if f2 is empty *)
    have Hneqj0 : wj != w0.
    { 
      apply: (@contra_neq _ _ ((proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; wj]) ((proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; w0]) _ _)=> [-> //|];
      have /eqP -> : (proper_to_edge_coloring (k_to_proper_coloring kc)) [set v; w0] == None by move/eqP: (w0_col_extended kc').
      by rewrite Hkcj.
    }
    by rewrite -(fan_last fmax) -(last_cons w w) fsplit cats1 last_rcons eq_refl in Hneqj0.
  (* so f2 is non-empty, i.e. wi != w0 *)
  have Habwi0 : Some ck \in absent_set kc wi.
  { 
    move: fsplit. 
    by case: f1=> [|wk f1']; [rewrite cat0s|]; 
    case=> Hw Hfval; have := fanW fmax;
    rewrite Hfval /absent_prop; [rewrite Hw | rewrite -cat_rcons cat_path last_rcons];
    rewrite /path Hkcj=> /andP[_ +] //; move=> /andP[-> _]. 
  }
  rewrite -[wj :: wi :: f2']cat1s catA in fsplit.
  have fsmallest := sub_fan fsplit.

  (* Construct ck cv Kempe Chain containing v *)
  pose chain := kempe_chain kc (Some ck) cv v.
  set ic := invertedChain (kempe_chain kc (Some ck) cv v).
  have imset_kc_ic : kc[E(G)] = ic[E(G)] := imset_eq_invert erefl (absent_in_imset Habwi0) (absent_in_imset Habv1).
  set ipc : properEdgeColoringType G (projT1 kc) :=  
    (exist _ (ic) (@inverted_proper _ _ _ _ _ _ chain erefl (proj2_sig (k_to_proper_coloring kc)))).
  have card_ic : #|ic[E(G)]| == (max_degree G  + 1 + 1) by rewrite -imset_kc_ic card_k_col.
  pose ikc : kEdgeColoringType G (max_degree G + 1 + 1) := existT _ (projT1 kc) (exist _ ipc card_ic).
  have v_in_v := (@in_component_of (kempe_graph kc (Some ck) cv) v).
  have vwj_in_kempe : ([set v; wj] \in E(kempe_graph kc (Some ck) cv)) by rewrite mem_kempe Einj Hkcj eq_refl.
  have vwj_in_chain : ([set v; wj] \subset chain).
  {
    apply/subUsetP; rewrite 2!sub1set.
    split; first by exact: v_in_v.
    by apply (@edge_in_component (kempe_graph kc (Some ck) cv) _).
  }
  have ic_vwj_cv : ic [set v; wj] = cv by apply (iffLR (proj1 (is_kempe_edge erefl vwj_in_kempe vwj_in_chain))). 
  have ikc_fmax : Fan ikc v w0 w := @inverted_fan _ _ _ _ _ _ chain erefl _ _ fmax (proj2_sig (k_to_proper_coloring kc)) (or_intror Habv1).
  have ic_va_ck : Some ck \in absent_set ikc v.
  {
    have [_ H] := @in_inverted_absent _ _ _ _ _ _ chain erefl _ v_in_v.
    by apply H.
  }
  case: (boolP (wi \in chain))=> wi_nin_v; exists (max_degree G + 1).
  - have w_nin_v : w \notin chain by admit.
    rewrite (notin_inverted_absent erefl w_nin_v imset_kc_ic) in Habw0.
    have Hcap : (Some ck \in absent_set ikc v :&: absent_set ikc w) by apply/setIP/(conj ic_va_ck Habw0).
    by have := (smaller_coloring ikc_fmax erefl Hcap).
  - rewrite (notin_inverted_absent erefl wi_nin_v imset_kc_ic) in Habwi0.
    rewrite {}(invert_fan_nodes HaisMax fmax ikc_fmax) in fsplit.
    have ikc_fsmallest : Fan ikc v w0 wi := sub_fan fsplit.
    have Hcap : (Some ck \in absent_set ikc v :&: absent_set ikc wi) by apply/setIP/(conj Habv0 Habwi0).
    by have := (smaller_coloring ikc_fsmallest erefl Hcap).
Qed.

