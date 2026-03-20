From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PathHelpers.
    Variables (G : sgraph) (x y z : G) (p : Path x y).

    Lemma inInteriorP :
        reflect (z \in interior p) ((z != x) && (z != y) && (z \in p)).
    Proof. rewrite !inE negb_or; exact: idP. Qed.

    Lemma isplitInternal : 
        irred p -> z \in interior p ->
        exists (u v : G) (uz : u -- z) (zv : z -- v) (p1 : Path x u) (p2 : Path v y),
        p = pcat (pcat p1 (edgep uz)) (pcat (edgep zv) p2) /\ u != v.
    Proof.
        move=> Ip /inInteriorP /andP[/andP[xNz zNy] z_in_p]; rewrite eq_sym in xNz.
        case/(isplitP Ip) def_p1 : _ / z_in_p => [pl pr Ipl Ipr Iz].
        case: (splitR pl xNz) Ipl => u [pl'] [uz] El Ipl. 
        case: (splitL pr zNy) Ipr => v [zv] [pr'] [Er _] Ipr.
        exists u, v, uz, zv, pl', pr'.
        split; first by rewrite El Er.
        (* by contradiction if u = v *)
        apply/eqP=> eq_uv.
        have u_in_pl : u \in pl by rewrite El mem_pcat_edgeR path_end.
        have u_in_pr : u \in pr by rewrite eq_uv Er mem_pcat_edgeL path_begin.
        have := Iz u u_in_pl u_in_pr.
        by have /eqP := sg_edgeNeq uz.
    Qed.

    Lemma deg1_internal : #|N(z)| <= 1 -> irred p -> z \notin interior p. 
    Proof.
        move=> /leq_gtF deg1 Ip; apply/negP=> z_in_p.
        have [u [v] [uz] [zv] [p1] [p2] [pc uNv]] := isplitInternal Ip z_in_p.
        suff : 2 <= #|N(z)|; first by rewrite deg1.
        rewrite -(ltn_add2r 1) addn1.
        have -> : 2 = #|[set u; v]| by rewrite cards2 uNv.
        rewrite addn1 ltnS. 
        apply/subset_leqif_cards.
        by rewrite subUset 2!sub1set 2!in_opn sg_sym.
    Qed.

End PathHelpers.

Proposition shared_interior3 
    (G : sgraph) 
    (x y z : G) 
    (p : Path x y) 
    (q : Path x z) 
    :
    #|N(x)| = 1 -> #|N(y)| = 1 -> #|N(z)| = 1 ->
    x != y -> y != z -> x != z ->
    irred p -> irred q ->
    exists w : G, 3 <= #|N(w)|.
Proof.
    move=> /eq_leq degx /eq_leq degy /eq_leq degz xNy yNz xNz Ip Iq.
    have z_nin_p : z \notin p by have := deg1_internal degz Ip; rewrite !inE negb_and negb_or eq_sym xNz eq_sym yNz.
    have y_nin_q : y \notin q by have := deg1_internal degy Iq; rewrite !inE negb_and negb_or eq_sym xNy yNz.
    case: (splitL p xNy) => u [xu] [p'] [Epc _].
    case: (splitL q xNz) => u' [xu'] [q'] [Eqc _].
    have uEu' : u = u'.
    {
        move/card_le1_eqP: degx=> in_nx.
        have := in_nx u u'.
        rewrite 2!in_opn=> eq_uu'.
        by have := eq_uu' xu xu'.
    }
    have x_nin_p' : x \notin p' by rewrite Epc irred_edgeL in Ip; case/andP: Ip.
    have y_nin_q' : y \notin q' by move: y_nin_q; rewrite Eqc mem_pcat_edgeL negb_or=> /andP[_ ->].
    have /andP[x_nin_q' Iq'] : (x \notin q') && irred q' by rewrite Eqc irred_edgeL in Iq.
    have u_in_p' : u \in p' by rewrite path_begin.
    have u_in_q : u \in q by rewrite uEu' Eqc mem_pcat_edgeL path_begin.
    case: (split_at_last (p := p') u_in_q u_in_p') => v [p1] [p2] [def_p' v_in_q v_last].
    case/(isplitP Iq) def_q' : _ / v_in_q => [q1 q2 Iq1 Iq2 Iv].
    exists v.
    have [v_in_p' v_in_q'] : v \in p' /\ v \in q by rewrite def_p' def_q' 2!mem_pcat 2!path_end.
    have xNv : x != v by 
        apply/eqP=> xEv; rewrite -xEv in v_in_p'; rewrite v_in_p' in x_nin_p'.
    have vNy : v != y by 
        apply/eqP=> vEy; rewrite vEy in v_in_q'; rewrite v_in_q' in y_nin_q.
    have vNz : v != z by 
        apply/eqP=> vEz; rewrite vEz in v_in_p'; rewrite Epc mem_pcat_edgeL v_in_p' negb_or andbF in z_nin_p.
    case: (splitR q1 xNv) => vx [q1'] [vxv] def_q1.
    case: (splitL p2 vNy) => vy [vvy] [p2'] [def_p2 _].
    case: (splitL q2 vNz) => vz [vvz] [q2'] [def_q2 _].
    have [hwy [hwz hwx]] : vy \in N(v) /\ vz \in N(v) /\ vx \in N(v) by 
        rewrite 3!in_opn vvy vvz sg_sym.
    have [vx_in_q1 [vy_in_p2 vz_in_q2]] : vx \in q1 /\ vy \in p2 /\ vz \in q2 by
        rewrite def_q1 def_p2 def_q2 3!mem_pcat 3!path_begin.
    have vzNvx : vz != vx. 
    {
        apply/eqP=> /esym vxEvz; rewrite vxEvz in vx_in_q1. 
        have vzEv := Iv vz vx_in_q1 vz_in_q2.
        by have := (sg_edgeNeq vvz); rewrite vzEv eq_refl.
    }
    have vzNvy : vz != vy.
    {
        apply/eqP=> /esym vyEvz; rewrite vyEvz in vy_in_p2.
        have vz_in_q : vz \in q by rewrite def_q' mem_pcat vz_in_q2.
        have vyEv := v_last vz vz_in_q vy_in_p2.
        by have := (sg_edgeNeq vvz); rewrite vyEv eq_refl. 
    } 
    have vxNvy : vx != vy.
    {
        apply/eqP=> vxEvy; rewrite vxEvy in vx_in_q1.
        have vy_in_q : vy \in q by rewrite def_q' mem_pcat vx_in_q1.
        have vyEv := v_last vy vy_in_q vy_in_p2.
        by have := (sg_edgeNeq vvy); rewrite vyEv eq_refl. 
    }
    rewrite -(ltn_add2r 1).
    have -> : 2 + 1 = #|[set vz; vx; vy]|.
    {
        have [djzy djxy] : [disjoint [set vz] & [set vy]] /\ [disjoint [set vx] & [set vy]] by do 2 rewrite disjoints1 -in_setC in_setC1. 
        by rewrite (@cardsU _ [set vz; vx] _) setIUl (disjoint_setI0 djzy) (disjoint_setI0 djxy) set0U cards0 cards1 cards2 vzNvx.
    }
    rewrite addn1 ltnS.
    apply/subset_leqif_cards.
    by rewrite 2!subUset 3!sub1set 3!in_opn vvz sg_sym.
Qed.

Definition pathp_edge {G : sgraph} (x u v : G) (s : seq G) : Prop :=
    exists i, (i < size s) && (nth x (x::s) i == u) && (nth x s i == v).

Definition Path_edge {G : sgraph} {x y : G} (p : Path x y) (u v : G) := pathp_edge x u v (tail p).

Section PathEdge.
    Variables (G : sgraph) (x y z u v : G) (p : Path x y).

    Lemma is_path_edge : Path_edge p u v -> u -- v.
    Proof.
        rewrite/Path_edge/pathp_edge=> [[i] /andP[/andP[Hs /eqP <-] /eqP <-]].
        move: (pathpW (valP p))=> /pathP Hp.
        exact: Hp x i Hs.
    Qed.

    Lemma not_path_edge :
        ~ u -- v -> ~ Path_edge p u v.
    Proof.
        apply/contra_not; exact: is_path_edge.
    Qed.

    Lemma vert_not_in_path :
        (u \notin p) \/ (v \notin p) -> ~ Path_edge p u v.
    Proof.
        case=> Hn [i /andP[/andP[Hs /eqP Hnl] /eqP Hnr]];
        [have Hin : u \in p | have /(mem_tail x) Hin : v \in tail p].
        - have /(mem_nth x) : i < size (x :: tail p) by
            move/(ltn_addr 1): Hs; 
            rewrite [size (tail p) + 1]addnC -[1 + size (tail p)]/(size([::x]) + size (tail p)) -size_cat.
        by rewrite Hnl -nodesE.
        - by rewrite Hin in Hn.
        - rewrite -Hnr; exact: (mem_nth x Hs).
        - by rewrite -nodesE in Hin; rewrite Hin in Hn.
    Qed.

    Lemma edgep_path_edge (xy : x -- y) :
        (Path_edge (edgep xy) u v) <-> ((x == u) && (y == v)).
    Proof.
        rewrite/Path_edge/pathp_edge /=;
        split=> [[i]| Heq]; by [case i | exists 0].
    Qed.

    Lemma cat_path_edge (q : Path y z) :
        Path_edge (pcat p q) u v <-> Path_edge p u v \/ Path_edge q u v.
    Proof.
        rewrite/Path_edge -[tail (pcat p q)]/((tail p) ++ (tail q)) /pathp_edge size_cat;
        split=> [[i] /andP[/andP[Hs +] +] |].
        - rewrite nth_cat (nth_cat x (x :: tail p) (tail q) i).
        case Hi: (i < size (tail p)).
        + have Hlt : size (tail p) < size (x :: tail p) by [].
            have -> := leq_ltn_trans (ltnW Hi) Hlt=> Hnl Hnr.
            left; exists i; by rewrite Hi Hnl Hnr.
        + move/negbT: Hi; rewrite -leqNgt -cat1s size_cat /= ltnS => Hi Hnl Hnr.
            right; exists (i - size (tail p)).
            rewrite -(ltn_subLR (size (tail q)) Hi) in Hs.
            rewrite Hs (set_nth_default x y Hs) {}Hnr /= andbT.
            rewrite leq_eqVlt in Hi; move/orP: Hi Hnl=> [/eqP Hi | Hi];
            [move/esym/eq_leq: (Hi) | move/ltn_geF: (Hi)]=> ->.
            - have/eqP H0 : (size (tail p) - size (tail p)) == 0 by rewrite subn_eq0.
            by rewrite -Hi -last_nth path_last /= H0 nth0 => /eqP <-.
            - rewrite -cat1s nth_cat -[_ < 1]/(_ == 0) subn1 subn_eq0 leqNgt Hi /=.
            have Hlt : (i - size (tail p) - 1) < size (tail q) by rewrite subn1; exact: (leq_ltn_trans (leq_pred (i - size (tail p))) Hs).
            by rewrite (set_nth_default x y Hlt) addnC subnDA.
        - case; move=> [i] /andP[/andP[Hi Hnl] Hnr];
            [exists i | exists (size (tail p) + i)]; rewrite -cat1s catA 2!(@nth_cat _ _ _ (tail q) _) size_cat /=;
            first by rewrite Hi (ltn_addl _ Hi) (ltn_addr _ Hi).
            rewrite ltn_add2l addnC ltn_add2r (@ltnNge _ (size (tail p))) leq_addl -[i + size (tail p) - size (tail p)]addnBA //= subnn addn0 (set_nth_default y x Hi) Hi Hnr andTb andbT.
            case Hs: (i == 0). 
            move/eqP: Hs Hnl=> -> /=.
            rewrite add0n -(@cat1s _ x _) nth_cat /=.
            case Hp: (size (tail p) < 1)=> /eqP <-; last by rewrite subn1 nth_last path_last.
            rewrite -[_ < 1]/(_ <= 0) in Hp.
            have Hxy: x = y.
            {
                have := leq_trans (idx_mem (path_end p)) Hp;
                rewrite -[_ <= 0]/(_ == 0) subn0  -(idx_start p);
                move/eqP/esym=> +. apply (idx_inj (path_begin p)).
            }
            by move/eqP: Hp Hxy; rewrite subn0 => -> ->.
            - move/neq0_lt0n: Hs Hnl=> Hs.
                have Hilts : i - 1 < size (tail q) by rewrite -ltn_predL -subn1 in Hs; exact: (ltn_trans Hs Hi).
                rewrite -cat1s nth_cat ltnS leqNgt Hs /=.
                by rewrite subnDr (set_nth_default y x Hilts).
    Qed.

End PathEdge.

Lemma idp_path_edge {G : sgraph} (x u v : G) : Path_edge (idp x) u v -> False.
Proof. by rewrite/Path_edge/pathp_edge /= => [[_]]. Qed.
