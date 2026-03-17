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

  Lemma in_chain x : x \in kempe_chain x.
  Proof. exact: in_component_of. Qed.

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

  Lemma inverted_fan {v : G} (fan : Fan c x v u) : 
    (ca \in absent_set c x) \/ (cb \in absent_set c x) -> 
    exists ifan : Fan invertedChain x v u, fval fan = fval ifan.
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

  Lemma deg_kempe u : 
    #|N(kempe_graph pc ca cb;u)| <= 2.
  Proof.
    rewrite -card_edge_neigh.
    rewrite -(card_in_imset (@injective_in_kempe u)).
    apply: (@leq_trans #|[set ca; cb]| _ _); last first.
    - rewrite cards2; by case: (ca == cb).
    apply/subset_leq_card/subsetP=> col /imsetP [e + ->].
    by rewrite !inE mem_edge_graph (@mem_kempe G _ pc ca cb _)=> /andP[/andP[_ ->] _].
  Qed.

  Lemma inverted_proper : 
    is_proper_edge_coloring (invertedChain chain).
  Proof. 
  Admitted.

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
    move=> uNv vNw uNw [/deg_chain_endpt degu [/deg_chain_endpt degv /deg_chain_endpt degw]].
    rewrite chain_x.
    case: (boolP (u \in kempe_chain pc ca cb x)) => [u_in|u_nin]; last by left.
    case: (boolP (v \in kempe_chain pc ca cb x)) => [v_in|v_nin]; last by right; left.
    case: (boolP (w \in kempe_chain pc ca cb x)) => [w_in|w_nin]; last by right; right.
    move: (u_in) (v_in) (w_in); rewrite /kempe_chain=> /same_component comp_u.
    rewrite -comp_u=> /components_pblockP [p].

    have := shared_interior3 
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
  Admitted.

  (*
  x and y both degree 1 in chain
  path from x to y
  z also degree 1, wts not in chain
  suppose it is, then path x z and path y z (both irred)
  
  *)
End KempeProper.