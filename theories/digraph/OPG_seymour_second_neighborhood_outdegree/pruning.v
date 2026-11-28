(** * The pruning lemma

Lemma 3.1 of the paper of OpenAI: for any families [R] and [C] of pairs of vertices of a
digraph, there are conflict-free subfamilies retaining the initially conflict-free members,
with at most |H| + (number of points of Z left uncovered) deleted members.

Proof: [konig_bimatching] gives a matching M of the augmented graph and a vertex cover of at most |M|
non-isolated vertices; [aug_matching_card], [aug_matching_parts] and [corner_bound] give
|M| <= |Z| + |H|, hence the pruning by [pruning_of_cover].

Provenance: the paper "A proof of Seymour's second-neighborhood conjecture" of OpenAI, a
model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and its Lean formalization (Pruning.lean, AugmentedRankBound.lean),
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
which proves the full statement of the conjecture.  The Lean development and the paper first
choose a maximum matching whose two auxiliary parts are maximum; this is not needed here, since
[corner_bound] holds for every matching. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import konig.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import
  defs augmented rankbound.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem pruning (G : diGraph) (R C : {set G * G}) :
  exists R' C' : {set G * G}, pruning_result R C R' C'.
Proof.
have [M [A [B [mM cov AM Ane Bne]]]] := konig_bimatching (aug_edge R C).
have [mO ma mb Oa Ob] := aug_matching_parts mM.
exists (R :\: [set a | inl a \in A]), (C :\: [set b | inl b \in B]).
apply: pruning_of_cover cov _ Ane Bne; apply: leq_trans AM _.
by apply: leq_trans (aug_matching_card mM) _; apply: corner_bound.
Qed.
