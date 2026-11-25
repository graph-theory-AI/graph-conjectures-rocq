(** * Unavoidability and vertex deletion

Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, "Blow-ups and extensions of trees in
tournaments", 2024, arXiv:2410.23566, Conjecture 9 (2410.23566__03).

A digraph D is p-unavoidable if every tournament on p vertices contains D as a (not necessarily
induced) subdigraph.  The unavoidability unvd(D) is the least such p; it exists if and only if D is
acyclic.

Conjecture 9: there exists a constant C such that unvd(D) <= C unvd(D - v) for every acyclic digraph
D and every vertex v of D.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  "unvd(D) = N" is the relation [unavoidability_number D N].  D is assumed to have at
least two vertices, as otherwise unvd(D) = 1 and unvd(D - v) = 0. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** Each tournament on [N] vertices contains [D]. *)
Definition tournament_unavoidable (D : diGraph) (N : nat) : Prop :=
  forall T : diGraph, tournament T -> #|T| = N -> subdigraph D T.

(** [N] is the least number such that each tournament on [N] vertices contains [D]. *)
Definition unavoidability_number (D : diGraph) (N : nat) : Prop :=
  tournament_unavoidable D N /\ (forall M : nat, M < N -> ~ tournament_unavoidable D M).

(** ** Statement *)

Definition AX_unavoidability_vertex_deletion_ratio_bounded : Prop :=
  exists C : nat, forall (D : diGraph) (v : D), acyclic D -> 1 < #|D| ->
    forall N M : nat,
      unavoidability_number D N -> unavoidability_number (induced [set~ v]) M -> N <= C * M.
