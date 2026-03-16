From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import edone preliminaries digraph sgraph.
Require Import aux edge_coloring fans.
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
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType) (x : G) (chain : {set kempe_graph c ca cb}).
  Hypothesis chain_x : chain = kempe_chain c ca cb x.

  (* techincally, just e \in subset kc could be enough, but this will be easier to reason about *)
  Definition invertedChain (e : {set G}) :=
    if ((e \in E(kempe_graph c ca cb)) && (e \subset chain)) then 
      if (c e == ca) then cb else ca
    else c e.

  Lemma imset_eq_invert : 
    ca \in c[E(G)] -> 
    cb \in c[E(G)] ->
    c[E(G)] = invertedChain[E(G)].
  Proof.
  Admitted.

  Lemma not_kempe_edge e :
    (e \notin E(kempe_graph c ca cb)) || ~~ (e \subset chain) ->
    c e = invertedChain e.
  Proof.
  Admitted.

  Lemma is_kempe_edge e : 
    (e \in E(kempe_graph c ca cb)) -> 
    (e \subset chain) -> 
    (c e = ca <-> invertedChain e = cb) /\
    (c e = cb <-> invertedChain e = ca).
  Proof.
  Admitted.

  Lemma in_inverted_absent (u : G) :
    u \in chain -> 
    (ca \in absent_set c u <-> cb \in absent_set invertedChain u) /\
    (cb \in absent_set c u <-> ca \in absent_set invertedChain u).
  Proof.
  Admitted.

  Lemma notin_inverted_absent (u : G) :
    u \notin chain -> 
    c[E(G)] = invertedChain[E(G)] ->
    absent_set c u = absent_set invertedChain u.
  Proof.
  Admitted.

  Lemma inverted_proper : 
    is_proper_edge_coloring c -> is_proper_edge_coloring invertedChain.
  Proof. 
  Admitted.

  Lemma inverted_fan {u v : G} (fan : Fan c x v u) : 
    is_proper_edge_coloring c ->   
    (ca \in absent_set c x) \/ (cb \in absent_set c x) -> 
    exists ifan : Fan (invertedChain) x v u, fval fan = fval ifan.
  Proof.
  Admitted.

  Definition chain_endpt (u : G) :=
    (ca \in absent_set c u) \/ (cb \in absent_set c u). 

  Lemma chain_endptP (u : G) :
    (ca \in absent_set c u) \/ (cb \in absent_set c u) -> chain_endpt u.
  Proof. by []. Qed.

  Proposition chain_two_endpts (u v w : G) :
    chain_endpt u /\ chain_endpt v /\ chain_endpt w ->
    (u \notin chain) \/ (v \notin chain) \/ (w \notin chain).
  Proof.
  Admitted.

  (*
  x and y both degree 1 in chain
  path from x to y
  z also degree 1, wts not in chain
  suppose it is, then path x z and path y z (both irred)
  
  *)

End InvertChain.