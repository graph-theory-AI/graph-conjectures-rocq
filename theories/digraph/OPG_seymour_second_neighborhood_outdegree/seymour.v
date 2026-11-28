(** * Seymour's second neighbourhood conjecture

Every nonempty oriented graph has a vertex whose out-degree is at most its second out-degree.

Idea.  By induction on the number of vertices, then on the number of arcs, a counterexample D is
minimal: smaller digraphs and digraphs obtained by deleting arcs have a good vertex.  Then D has
positive in-degrees and the subset deficit |F^2(S) \ F(S)| < |F(S) \ S| for every nonempty
proper set S of vertices (reduction.v, F(S) the set of out-neighbours of S).  Its blow-up by
transitive tournaments of size |D| + 1 has positive in-degrees and the strict subset growth
|U| + |F^2(U)| < 2 |F(U)| (blowup.v).  No digraph has it (extremal.v): an extremal pair of
families of pairs of vertices is improved by the pruning lemma (pruning.v), whose proof bounds
the matchings of an auxiliary bipartite graph by ranks of matrices with generic coefficients
(mxmaps.v, coeffs.v, rankbound.v, augmented.v, with König's theorem and the linear algebra of
GraphLib/konig.v and GraphLib/linear_algebra.v).

Provenance.  The proof follows the paper of OpenAI, "A proof of Seymour's second-neighborhood
conjecture" (September 23, 2026), a model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and is organized after its Lean formalization,
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
(here: Main.lean, Reduction.lean, ReductionCore.lean).  The Lean development proves the full
statement of the conjecture, that of the comparator challenge
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SeymourSecondNeighborhood.lean
which is the statement of main.v.  The rank bound of the pruning lemma (rankbound.v) is simpler
than in the paper: it holds for every matching of the auxiliary graph and needs no maximum
matching. *)

From GraphTheory Require Import digraph.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require Import
  defs reduction blowup extremal.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A minimal counterexample is impossible. *)
Lemma no_minimal_counterexample (D : diGraph) :
  oriented D -> 0 < #|D| -> order_minimal D -> arc_minimal D -> exists v : D, good v.
Proof.
move=> oD D0 omin amin; case: (boolP [exists v : D, good v]) => [/existsP //|].
rewrite negb_exists => bad; have [pD dD] := minimal_subset_deficit oD D0 bad omin amin.
case: (@no_strict_growth (tt_blowup D #|D|.+1)).
- exact: tt_blowup_oriented.
- by rewrite card_prod card_ord muln_gt0 D0.
- exact: tt_blowup_positive_indeg.
- exact: tt_blowup_strict_growth.
Qed.

(** Induction on the number of vertices, then on the number of arcs (the arc deletions keep the
    vertex set). *)
Theorem seymour_second_neighbourhood : main.OPG_seymour_second_neighborhood_outdegree.
Proof.
suff h n k (D : diGraph) : #|D| < n -> num_edges D < k -> oriented D -> 0 < #|D| ->
    exists v : D, good v.
  by move=> D; apply: (h #|D|.+1 (num_edges D).+1).
elim: n k D => // n IHn; elim=> // k IHk D Dn Dk oD D0.
apply: no_minimal_counterexample => //.
  move=> D' oD' D'0 D'D; apply: (IHn (num_edges D').+1) => //.
  by rewrite (leq_trans D'D) // -ltnS.
move=> F FD; apply: IHk => //; last exact: oriented_del_arcs.
by rewrite (leq_trans (num_edges_del_arcs FD)) // -ltnS.
Qed.
