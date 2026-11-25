(** * Induced-saturated infinite tournaments

Bonamy, Groenland, Johnston, Morrison, Scott, "Infinite induced-saturated graphs", arXiv:2506.08810,
Conjecture 24 (2506.08810__03).

A locally finite perturbation of a tournament is obtained by reversing the arcs of a nonempty,
possibly infinite, set such that every vertex is in finitely many of these arcs.  A tournament is
T-free if it has no subtournament isomorphic to T.

Conjecture: let T be a finite tournament that is not transitive.  Then there is a countably infinite
T-free tournament S such that every locally finite perturbation of S has a subtournament isomorphic
to T.

Encoding.  Finite tournaments are digraphs of GraphTheory ([diGraph]).  The vertices of a countably
infinite tournament are the natural numbers.  A locally finite perturbation is a tournament that
differs from the given one on the arc between some two vertices and, for each vertex v, on the arcs
between v and finitely many vertices only (the arcs between v and the sufficiently large vertices
are unchanged). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** ** Definitions specific to the conjecture *)

(** [S] is a tournament on the natural numbers. *)
Definition nat_tournament (S : rel nat) : Prop :=
  irreflexive S /\ forall x y : nat, (x != y) = S x y (+) S y x.

(** The tournament [S] has a subtournament isomorphic to [T]. *)
Definition has_subtournament (T : diGraph) (S : rel nat) : Prop :=
  exists f : T -> nat, injective f /\ forall x y : T, x != y -> (x -- y) = S (f x) (f y).

(** [S'] is a locally finite perturbation of the tournament [S]. *)
Definition locally_finite_perturbation (S S' : rel nat) : Prop :=
  [/\ nat_tournament S',
      exists x y : nat, x != y /\ S x y != S' x y
    & forall v : nat, exists N : nat, forall u : nat, N <= u -> S' v u = S v u].

(** ** Statement *)

Definition AX_induced_saturated_infinite_tournament_perturbation : Prop :=
  forall T : diGraph,
    tournament T -> ~ transitive (@edge_rel T) ->
    exists S : rel nat,
      [/\ nat_tournament S, ~ has_subtournament T S
        & forall S' : rel nat, locally_finite_perturbation S S' -> has_subtournament T S'].
