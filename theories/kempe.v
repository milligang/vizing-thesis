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
  Variables (G : sgraph) (ColorType : finType) (c : edgeColoringType G ColorType) (ca cb : ColorType) (x : G).
  Let kc := kempe_chain c ca cb x.
  
  (* techincally, just e \in subset kc could be enough, but this will be easier to reason about *)
  Definition invertedChain (e : {set G}) :=
    if ((e \in E(kempe_graph c ca cb)) && (e \subset kc)) then 
      if (c e == ca) then cb else ca
    else c e.

  Lemma sub_imset_eq_invert : 
    c[E(G)] :\: ([set ca] :|: [set cb]) = invertedChain[E(G)] :\: ([set ca] :|: [set cb]).
  Proof.
  Admitted.

  Lemma imset_eq_invert : 
    ca \in c[E(G)] -> cb \in c[E(G)] ->
    c[E(G)] = invertedChain[E(G)].
  Proof.
  Admitted.

  Lemma not_kempe_edge e :
    e \notin E(kempe_graph c ca cb) -> c e = invertedChain e.
  Proof.
  Admitted.

  Lemma is_kempe_edge e : e \in E(G) ->
    (c e = ca <-> invertedChain e = cb) /\
    (c e = cb <-> invertedChain e = ca).
  Proof.
  Admitted.

  Lemma inverted_proper : 
    is_proper_edge_coloring c -> is_proper_edge_coloring invertedEdgeColoring.
  Proof. 
  Admitted.

End InvertChain.