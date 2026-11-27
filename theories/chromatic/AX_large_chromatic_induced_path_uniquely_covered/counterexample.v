(** * The question has a negative answer for paths with three vertices

    The counterexamples are discrete Borsuk graphs [G] ([borsuk_graph.v]), with the cover by the
    upsets of a relation on the vertices ([obstruction.v]): two vertices with a common neighbour
    are near each other; a colouring of the grid in which near vertices have distinct colours
    gives an orientation of these pairs, and the upsets are stable because they have a small
    diameter whereas the ends of an edge are almost antipodal.

    The idea of the upsets comes from Graph-Theory-LLM-Proofs (attacks/1702.01094__01), where
    the graphs are random graphs of bounded degree and large girth; it was formalized in
    graph-theory-rocq (chromatic-theory/theories/applications/uniquely_covered_paths). *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic(chi_leP, proper_coloringP).
From GC.chromatic.AX_large_chromatic_induced_path_uniquely_covered Require Import
  main(AX_large_chromatic_induced_path_uniquely_covered) borsuk_graph obstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma not_uniquely_covered : ~ AX_large_chromatic_induced_path_uniquely_covered.
Proof.
move=> /(_ 3)[t]; set l := 2 ^ t; set m := (2 ^ t * far_dist t l).+1.
pose G := borsuk_graph t m l; pose r : rel G := @step t m l.
have comp : forall u v w : G, u -- v -> v -- w -> connect r u w || connect r w u.
  exact: step_comparable.
have stab : forall x : G, stable [set y | connect r x y] := @step_stable t m l.
case/(_ G G (fun x => [set y | connect r x y])) => [||//||p [sz_p [uniq_p path_p _]]].
- exact: upset_triangle_free comp stab.
- apply/ltnW; rewrite ltnNge; apply/negP => /chi_leP[col /proper_coloringP].
  exact: borsuk_coloring.
- by move=> v; exists v; rewrite inE connect0.
by apply: upset_not_uniquely_covered comp _ _ uniq_p path_p; rewrite sz_p.
Qed.
