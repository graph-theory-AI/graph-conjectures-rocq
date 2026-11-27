(** * Polynomial unavoidability of the digraphs of bounded maximum average degree

Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, "Blow-ups and extensions of trees in
tournaments", 2024, arXiv:2410.23566, Problem 6 (2410.23566__00).

A digraph D is p-unavoidable if every tournament on p vertices contains D as a (not necessarily
induced) subdigraph.  The unavoidability unvd(D) is the least such p; it exists if and only if D is
acyclic.  The maximum average degree of a digraph is the maximum of 2|A(H)|/|V(H)| over its
nonempty subdigraphs H.

Problem 6: let α be a positive real number.  Does there exist a polynomial P such that
unvd(D) <= P(|V(D)|) for every (acyclic) digraph D of maximum average degree at most α?  The
proposition states a positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  "unvd(D) = N" is the relation [unavoidability_number D N], so that the digraphs that
are not acyclic are ignored.  The number α is rational, which is equivalent, and not necessarily
positive.  The polynomial has the form a n^d + b, with natural coefficients, which is equivalent as
every polynomial is bounded by one of this form on the natural numbers. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** Each tournament on [N] vertices contains [D]. *)
Definition tournament_unavoidable (D : diGraph) (N : nat) : Prop :=
  forall T : diGraph, tournament T -> #|T| = N -> subdigraph D T.

(** [N] is the least number such that each tournament on [N] vertices contains [D]. *)
Definition unavoidability_number (D : diGraph) (N : nat) : Prop :=
  tournament_unavoidable D N /\ (forall M : nat, M < N -> ~ tournament_unavoidable D M).

(** ** Definitions copied from GraphLib/fractional.v *)

(** Maximum average degree: the maximum of 2|A(S)|/|S| over nonempty [S] (0 if [D] is empty). *)
Definition digraph_mad (D : diGraph) : rat :=
  (\big[Num.max/0]_(S in [set S : {set D} | S != set0])
     ((2 * num_edges (induced S))%:Q / (#|S|)%:Q))%R.

(** ** Statement *)

Definition AX_unavoidability_bounded_average_degree_polynomial : Prop :=
  forall alpha : rat, exists a d b : nat, forall (D : diGraph) (N : nat),
    (digraph_mad D <= alpha)%R -> unavoidability_number D N -> N <= a * #|D| ^ d + b.
