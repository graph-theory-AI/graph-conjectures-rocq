(** * Arc-disjoint transitive triples in tournaments

Yuster, "The number of edge-disjoint transitive triples in a tournament", Discrete Math. 287
(2004); Open Problem Garden,
minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament.

A tournament is an orientation of a complete graph.  A transitive subtournament of order 3 consists
of three vertices a, b, c with the arcs a -> b, b -> c and a -> c.

Conjecture: a tournament of order n contains ⌈n(n-1)/6 - n/3⌉ arc-disjoint transitive
subtournaments of order 3.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  The bound is ⌈n(n-3)/6⌉, as
n(n-1)/6 - n/3 = n(n-3)/6.  The subtraction n - 3 is that of natural numbers: the bound is 0 for
n < 3, where ⌈n(n-3)/6⌉ = 0 too. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** ** Definitions specific to the conjecture *)

(** The triple (a,b,c) is a transitive tournament: a -> b, b -> c and a -> c. *)
Definition transitive_triple (D : diGraph) (t : D * D * D) : bool :=
  [&& t.1.1 -- t.1.2, t.1.2 -- t.2 & t.1.1 -- t.2].

(** The three arcs of the transitive triple [t]. *)
Definition triple_arcs (D : diGraph) (t : D * D * D) : {set D * D} :=
  [set (t.1.1, t.1.2); (t.1.2, t.2); (t.1.1, t.2)].

(** ** Statement *)

Definition OPG_tournament_arc_disjoint_transitive_triples : Prop :=
  forall T : diGraph, tournament T ->
    exists P : seq (T * T * T),
      [/\ all (@transitive_triple T) P,
          pairwise (fun a b => [disjoint triple_arcs a & triple_arcs b]) P
        & ceil_div (#|T| * (#|T| - 3)) 6 <= size P].
