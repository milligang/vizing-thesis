From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import sgraph digraph.

Definition edge_neigh {G : sgraph} (u : G) := [set e in E(G) | u \in e].
Notation "E{ x }" := (edge_neigh x) (at level 0, format "E{ x }").