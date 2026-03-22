From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux spath edge_coloring fans.
From Equations Require Import Equations.

Set Warnings "-notation-overridden, -notation-incompatible-prefix".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section KempeGraph.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType).
  Implicit Types (x y : G) (e : {set G}).

  (* A Kempe graph will consist of all ca-cb kempe chains in the graph *)
  Definition kempe_rel := [rel x y : G | x -- y && ((c [set x; y] == ca) || (c [set x; y] == cb))].

  Lemma kempe_sym : symmetric kempe_rel.  
  Proof. by move=> x y /=; by rewrite sgP setUC. Qed. 
         
  Lemma kempe_irrefl : irreflexive kempe_rel.  
  Proof. by move => x /=; rewrite sgP. Qed.

  Definition kempe_graph := @SGraph G kempe_rel kempe_sym kempe_irrefl.

  Lemma mem_kempe e : e \in E(kempe_graph) = (e \in E(G)) && ((c e == ca) || (c e == cb)).
  Proof.
    apply/edgesP/andP => [[x] [y] [-> /andP[xy xyc]]|[]]; first by rewrite in_edges.
    by move/edgesP => [x] [y] [-> xy xyNA]; exists x,y; split => //; apply/andP.  
  Qed.

  Lemma kempe_opn x z : 
    z \in N(kempe_graph;x) = (z \in N(G;x)) && ((c [set x; z] == ca) || (c [set x; z] == cb)).
  Proof. by rewrite !inE -in_edges mem_kempe in_edges. Qed.

  Lemma kempe_sub : E(kempe_graph) \subset E(G).
  Proof. by apply/subsetP=> e; rewrite mem_kempe => /andP[]. Qed.

  Lemma kempe_edgeN e : (c e != ca) -> (c e != cb) -> e \notin E(kempe_graph).
  Proof. by rewrite mem_kempe negb_and negb_or=> -> ->. Qed.
    
  (* A kempe chain is a single component of a kempe graph containing a given vertex *)
  Definition kempe_chain x := @component_of kempe_graph x.

  Lemma edge_in_component (H : sgraph) (u v : H) :
    [set u; v] \in E(H) -> v \in component_of u.
  Proof.
    rewrite in_edges=> /edgep p.
    by apply/components_pblockP; exists p.
  Qed.

End KempeGraph.

Section InvertGraph.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType).

  Definition invertedKempeGraph (e : {set G}) :=
    if (e \in E(kempe_graph c ca cb)) then 
      if (c e == ca) then cb else ca
    else c e.
  
  Lemma mem_invert_ab : 
    (ca \in c[E(G)] <-> cb \in invertedKempeGraph[E(G)]) /\
    (cb \in c[E(G)] <-> ca \in invertedKempeGraph[E(G)]).
  Proof.
    rewrite/invertedKempeGraph.
    split;
    (split=> [/in_c_all_edgeP [e] in_e ce_abP|/in_c_all_edgeP [e]];
    [
      (* forward direction *)
      move/eqP: (ce_abP)=> ce_ab;
      apply/in_c_all_edgeP; exists e; first by [];
      have ->: e \in E(kempe_graph c ca cb) by rewrite mem_kempe in_e ce_ab
    |
      (* reverse direction *)
      rewrite mem_kempe=> in_e; rewrite in_e /=;
      case ce_a: (c e == ca)=> /=; move/eqP: ce_a=> ce_a;
      case ce_b: (c e == cb)=> /=; move/eqP: ce_b=> ce_b;
      move=> contra; apply/in_c_all_edgeP; exists e=> //
    ]);
    first by rewrite ce_ab.
    - rewrite contra in ce_a; contradiction.
    - by case ce_a: (c e == ca)=> /=; move/eqP: ce_a=> ce_a; rewrite ce_abP in ce_a.
    - by rewrite contra.
  Qed.

End InvertGraph. 

Section InvertChain.
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType) (x : G) (chain : {set kempe_graph c ca cb}) (u : G).
  Hypothesis chain_x : chain = kempe_chain c ca cb x.

  (* techincally, just e \in subset kc could be enough, but this will be easier to reason about *)
  Definition invertedChain (e : {set G}) :=
    if ((e \in E(kempe_graph c ca cb)) && (e \subset chain)) then 
      if (c e == ca) then cb else ca
    else c e.

  Lemma imset_invert_sub : 
    ca \in c[E(G)] -> 
    cb \in c[E(G)] ->
    invertedChain[E(G)] \subset c[E(G)].
  Proof.
    rewrite /invertedChain=> /in_c_all_edgeP [ea] ea_in_e ea_ca /in_c_all_edgeP [eb] eb_in_e eb_cb.
    apply/subsetP=> c0 /in_c_all_edgeP [e] e_in_e <-. 
    apply/in_c_all_edgeP.
    case e_in_chain: ((e \in E(kempe_graph c ca cb)) && (e \subset chain)); last by exists e; rewrite // e_in_chain.
    move: e_in_chain; rewrite mem_kempe=> /andP[/andP[_ /orP[/eqP ->|/eqP ->]] e_in_chain];
    [rewrite eq_refl | case ca_cb : (cb == ca); last by exists ea]; by exists eb.
  Qed.

  Lemma not_kempe_edge e :
    (e \notin E(kempe_graph c ca cb)) \/ ~ (e \subset chain) ->
    c e = invertedChain e.
  Proof.
    by case=> [|/negP] not_in; rewrite /invertedChain (negbTE not_in).
  Qed.

  Lemma is_kempe_edge e : 
    (e \in E(kempe_graph c ca cb)) -> 
    (e \subset chain) -> 
    (c e = ca <-> invertedChain e = cb) /\
    (c e = cb <-> invertedChain e = ca).
  Proof.
    rewrite /invertedChain mem_kempe=> /andP[-> /orP[e_c | e_c]] ->;
    split; split; move/eqP: (e_c)=> ->; rewrite eq_refl //= orbT /=;
    first by move=> ->; rewrite eq_refl.
    all: case eq_ab: (cb == ca); by move/eqP: eq_ab.
  Qed.

  Lemma in_inverted_absent :
    u \in chain -> 
    (ca \in absent_set c u <-> cb \in absent_set invertedChain u) /\
    (cb \in absent_set c u <-> ca \in absent_set invertedChain u).
  Proof.
  Admitted.

  Lemma notin_inverted_absent :
    u \notin chain -> 
    c[E(G)] = invertedChain[E(G)] ->
    absent_set c u = absent_set invertedChain u.
  Proof.
  Admitted.

  Lemma w0_inverted (w0 : G) :
    c [set u; w0] != ca -> c [set u; w0] != cb ->
    w0_prop c [set u; w0] -> w0_prop invertedChain [set u; w0].
  Proof.
  Admitted.

End InvertChain.

Section KempeProper.
  Variables (G : sgraph) (ColorType : finType) (pc : properEdgeColoringType G ColorType) (ca cb : ColorType) (x : G) (chain : {set kempe_graph pc ca cb}).
  Implicit Types (u : G).
  Hypothesis chain_x : chain = kempe_chain pc ca cb x.

  Lemma injective_in_kempe u :
    {in E{kempe_graph pc ca cb;u} &, injective (proj1_sig pc)}.
  Proof.
    move=> e1 e2; move: ((proj2_sig pc) u e1 e2).
    rewrite 4!mem_edge_graph 2!(@mem_kempe G _ pc ca cb _) => Hc /andP[/andP[? ?] ?] /andP[/andP[? ?] ?].
    exact: Hc.
  Qed.

  Lemma max_deg_kempe u : 
    #|N(kempe_graph pc ca cb;u)| <= 2.
  Proof.
    rewrite -card_edge_neigh.
    rewrite -(card_in_imset (@injective_in_kempe u)).
    apply: (@leq_trans #|[set ca; cb]| _ _); last first.
    - rewrite cards2; by case: (ca == cb).
    apply/subset_leq_card/subsetP=> col /imsetP [e + ->].
    by rewrite !inE mem_edge_graph (@mem_kempe G _ pc ca cb _)=> /andP[/andP[_ ->] _].
  Qed.

  Lemma min_deg_kempe u v :
    u \in chain -> v \in chain -> u != v -> 0 < #|N(kempe_graph pc ca cb;u)| /\ 0 < #|N(kempe_graph pc ca cb;v)|.
  Proof.
    rewrite chain_x /kempe_chain=> /same_component comp_u v_in uNv.
    have u_connect : connected (@component_of (kempe_graph pc ca cb) u) := @connected_component_of (kempe_graph pc ca cb) u.
    have u_in_u : u \in @component_of (kempe_graph pc ca cb) u := @in_component_of (kempe_graph pc ca cb) u.
    have v_in_u : v \in @component_of (kempe_graph pc ca cb) u by rewrite -comp_u in v_in.
    case: (path_in_connected u_connect u_in_u v_in_u)=> p Ip _.
    split; apply/card_gt0P.
    - case: (splitL p uNv)=> w [+] _.
      by exists w; rewrite in_opn.
    - case: (splitR p uNv) => w [_] [wv] _.
      by exists w; rewrite in_opn sg_sym.
  Qed.

  Lemma inverted_proper : 
    is_proper_edge_coloring (invertedChain chain).
  Proof.
    have := proj2_sig pc.
    rewrite /is_proper_edge_coloring /invertedChain => is_pc u e1 e2 e1_in_e e2_in_e.
    specialize (is_pc u e1 e2 e1_in_e e2_in_e);
    case e1_in_K: (e1  \in E(kempe_graph pc ca cb)); case e1_in_C: (e1 \subset chain);
    case e2_in_K: (e2  \in E(kempe_graph pc ca cb)); case e2_in_C: (e2 \subset chain)=> /=;
    try by exact: is_pc.
    - move: e1_in_K e2_in_K; rewrite 2!mem_kempe.
      case: ifP=> /eqP c_e1 /andP[e1_in_G /= /eqP ca_cb_e1]; [move: c_e1 | move: ca_cb_e1];
      case: ifP=> /eqP c_e2 + /andP[e2_in_G /= /eqP ca_cb_e2] ca_cb;
      rewrite -?ca_cb -?ca_cb_e2 -?c_e2; exact: is_pc.
    - have contra : e2 \subset chain.
      {
        move: e1_in_e e2_in_e e1_in_K e2_in_K e1_in_C e2_in_C
          => /edgesSetP [y1] [uy1 _] /edgesSetP [y2] [uy2 _].
        rewrite uy1 uy2 2!subUset 3!sub1set chain_x /kempe_chain
          => /edge_in_component _ /edge_in_component y2_in_u /andP[u_in_x _] _.
        have <- := (@same_component (kempe_graph pc ca cb) u x u_in_x).
        by rewrite (@in_component_of (kempe_graph pc ca cb) u) y2_in_u.
      }
      by rewrite contra in e2_in_C.
    1,2: 
      move: e2_in_e e2_in_K;
      rewrite mem_kempe mem_edge_graph=> /andP[-> _] /negbT;
      rewrite /= negb_or=> /andP[ca_e2 cb_e2];
      case: ifP=> _ contra; move: ca_e2 cb_e2; by rewrite contra eq_refl.
    - have contra : e1 \subset chain.
      {
        move: e1_in_e e2_in_e e1_in_K e2_in_K e1_in_C e2_in_C
          => /edgesSetP [y1] [uy1 _] /edgesSetP [y2] [uy2 _].
        rewrite uy1 uy2 2!subUset 3!sub1set chain_x /kempe_chain
          => /edge_in_component y1_in_u /edge_in_component _ _ /andP[u_in_x _].
        have <- := (@same_component (kempe_graph pc ca cb) u x u_in_x).
        by rewrite (@in_component_of (kempe_graph pc ca cb) u) y1_in_u.
      }
      by rewrite contra in e1_in_C.
    all:
      move: e1_in_e e1_in_K;
      rewrite mem_kempe mem_edge_graph=> /andP[-> _] /negbT;
      rewrite /= negb_or=> /andP[ca_e1 cb_e1];
      case: ifP=> _ contra; move: ca_e1 cb_e1; by rewrite contra eq_refl.
  Qed.

  Definition chain_endpt u :=
    (ca \in absent_set pc u) \/ (cb \in absent_set pc u).

  Lemma chain_endptP u :
    (ca \in absent_set pc u) \/ (cb \in absent_set pc u) -> chain_endpt u.
  Proof. by []. Qed.

  Lemma deg_chain_endpt u :
    chain_endpt u -> #|N(kempe_graph pc ca cb;u)| <= 1.
  Proof.
    rewrite -card_edge_neigh /chain_endpt -(card_in_imset (@injective_in_kempe u));
    case=> /absent_edge abs; [set cset := [set cb] | set cset := [set ca]];
    (apply: (@leq_trans #|cset| _ _); last by rewrite cards1);
    apply/subset_leq_card/subsetP=> col /imsetP [e + ->];
    rewrite mem_edge_graph (@mem_kempe G _ pc ca cb _)=> /andP[/andP[/edgesP [y] [z] [def_e yz] /orP[+|//]]];
    move: (yz); rewrite sg_sym -in_opn=> zy; rewrite -in_opn in yz;
    rewrite def_e=> /eqP ce /set2P[eq_u | eq_u];
    rewrite -eq_u in yz zy; 
    try by rewrite inE -ce.
    - have := abs z yz; by rewrite -ce eq_u eq_refl.
    - have := abs y zy; by rewrite -ce eq_u setUC eq_refl.
    - have := abs z yz; by rewrite -ce eq_u eq_refl.
    - have := abs y zy; by rewrite -ce eq_u setUC eq_refl.
  Qed.

  Proposition chain_two_endpts (u v w : G) :
    u != v -> v != w -> u != w ->
    chain_endpt u /\ chain_endpt v /\ chain_endpt w ->
    (u \notin chain) \/ (v \notin chain) \/ (w \notin chain).
  Proof.
    case: (boolP (u \in chain)) => [u_in|u_nin]; last by left.
    case: (boolP (v \in chain)) => [v_in|v_nin]; last by right; left.
    case: (boolP (w \in chain)) => [w_in|w_nin]; last by right; right.
    move=> uNv vNw uNw [/deg_chain_endpt + [/deg_chain_endpt + /deg_chain_endpt +]].
    rewrite leq_eqVlt (@leq_eqVlt #|N(kempe_graph pc ca cb;v)| _) (@leq_eqVlt #|N(kempe_graph pc ca cb;w)| _ ) 
            ltnNge (@ltnNge #|N(kempe_graph pc ca cb;v)| _) (@ltnNge #|N(kempe_graph pc ca cb;w)| _ ). 
    have [[-> ->] [_ ->]] := conj (min_deg_kempe u_in v_in uNv) (min_deg_kempe u_in w_in uNw).
    move: (u_in) (v_in) (w_in); rewrite chain_x /kempe_chain 3!orbF => /same_component comp_u + + /eqP degu /eqP degv /eqP degw.
    have u_in_u : u \in (@component_of (kempe_graph pc ca cb)) u by exact: (@in_component_of (kempe_graph pc ca cb) u).
    have u_connect : connected (@component_of (kempe_graph pc ca cb) u) by exact: connected_component_of.
    rewrite -comp_u=> v_in_u w_in_u.
    have [p Ip p_in_u] := path_in_connected u_connect u_in_u v_in_u.
    have [q Iq q_in_u] := path_in_connected u_connect u_in_u w_in_u.
    have [y /ltn_geF] := @shared_interior3 (kempe_graph pc ca cb) _ _ _ _ _ degu degv degw uNv vNw uNw Ip Iq.
    by have -> := max_deg_kempe y.
  Qed.

  (* Lemma inverted_fan {v : G} (fan : Fan c x v u) : 
  (ca \in absent_set c x) \/ (cb \in absent_set c x) -> 
  exists ifan : Fan invertedChain x v u, fval fan = fval ifan.
  Proof.
  Admitted. *)

  (* 
    Technically, the following is also true less hypotheses. 
    But since we only use this in the proof of vizing's theorem,
    we make this more specific (to not repeat our work from there)
  *)

  Lemma inverted_fan 
    {w0 wi wj w : G} {f1 f2 : seq G} 
    (imset_pc_ic : pc [E(G)] = (invertedChain chain) [E(G)])
    (fan : Fan pc x w0 w) 
    (fsplit : w :: \val fan = f1 ++ [:: wj,  wi  & f2])
    (jN0 : wj != w0)
    (pc_xa_cb : cb \in absent_set pc x)
    (pc_wia_ca : ca \in absent_set pc wi)
    (pc_wa_ca : ca \in absent_set pc w)
    (pc_xwj_ca : (sval pc) [set x; wj] = ca)
  : 
    exists (w' : G) (ifan : Fan (invertedChain chain) x w0 w'),
    (ca \in absent_set (invertedChain chain) w').
  Proof.
    rewrite -[wj :: wi :: f2]cat1s catA in fsplit.
    have wj_at_x : wj \in N(x).
    {
      apply/(@in_neigh _ _ _ _ _ _ fan); rewrite fsplit.
      by rewrite mem_cat cats1 mem_rcons in_cons eq_refl.
    }
    have w0_at_x : w0 \in N(x).
    {
      apply/(@in_neigh _ _ _ _ _ _ fan).
      by have := mem_last w (\val fan); rewrite fan_last.
    }
    have w0_ifan : w0_prop (invertedChain chain) [set x; w0].
    {
      apply/(w0_inverted chain_x _ _ (fan_w0_prop fan)).
      - rewrite -pc_xwj_ca. move: (wj_at_x). 
        suff : (sval pc [set x; w0]) \in absent_set pc wj;
        first by exact: absent_edge_sym.
        rewrite eq_sym in jN0.
        apply/(absent_del_edge _ _ (jN0)); first by rewrite in_edges -in_opn.
        + move: wj_at_x; by rewrite in_opn=> /sg_edgeNeq /negbT.
        exact: (fan_w0_prop fan).
      - rewrite eq_sym. apply/(absent_edge pc_xa_cb w0_at_x). 
    }
    case: (boolP (wi \in chain))=> wi_in_x.
    - have /andP[xNwi /andP[wiNw xNw]] : [&& x != wi, wi != w & x != w].
      {
        have w_in_f : w \in w::val fan by rewrite in_cons eq_refl.  
        have eq_fmax : val fan = behead ((f1 ++ [:: wj]) ++ wi :: f2) by rewrite -fsplit.
        have wi_in_fmax : wi \in val fan. 
        {
          rewrite eq_fmax; case: f1 fsplit eq_fmax=> [|hd tl] _; first by rewrite cat0s cat1s /behead in_cons eq_refl.
          by rewrite -catA cat_cons /behead catA mem_cat in_cons eq_refl.
        }
        have wi_in_f : wi \in w::val fan by rewrite in_cons wi_in_fmax.
        have := fan_uniq fan; rewrite cons_uniq=> /andP[w_nin_fmax _].
        case: (boolP (x != wi))=> [xNwi|/negbNE /eqP xEwi];
        [rewrite andTb; case: (boolP (wi != w))=> [wiNw|/negbNE /eqP wiEw];
          [rewrite andTb; case: (boolP (x != w))=> [xNw|/negbNE /eqP xEw]=> //;
            have := in_neigh w_in_f;
            rewrite in_opn xEw=> /sg_edgeNeq /eqP; contradiction
          | rewrite andFb; rewrite wiEw in wi_in_fmax; by rewrite (wi_in_fmax) in w_nin_fmax]
        |
          rewrite andFb; have := in_neigh wi_in_f;
          rewrite in_opn xEwi=> /sg_edgeNeq /eqP; contradiction
        ].
      }
      have x_in_x := (@in_component_of (kempe_graph pc ca cb) x).
      have w_nin_x : w \notin chain by
        case
          (@chain_two_endpts x wi w xNwi wiNw xNw
            (conj (chain_endptP (or_intror pc_xa_cb))
            (conj (chain_endptP (or_introl pc_wia_ca))
                  (chain_endptP (or_introl pc_wa_ca)))
          ));
        [rewrite chain_x /kempe_chain x_in_x | case; [rewrite wi_in_x|]].
      
      have ifan : fanp (invertedChain chain) (\val fan) x w0 w.
      {
        rewrite /fanp fan_last eq_refl fan_uniq fan_neigh w0_ifan //=.
        admit.
      }
      exists w, (Build_Fan ifan).
      by rewrite (notin_inverted_absent chain_x w_nin_x imset_pc_ic) in pc_wa_ca.
    - rewrite (notin_inverted_absent chain_x wi_in_x imset_pc_ic) in pc_wia_ca.
      have fsmaller := sub_fan fsplit.
      have ifan : fanp (invertedChain chain) (\val fsmaller) x w0 wi.
      {
        rewrite /fanp fan_last eq_refl fan_uniq fan_neigh w0_ifan //=.
        admit.
      }
      by exists wi, (Build_Fan ifan).
    Admitted.

End KempeProper.