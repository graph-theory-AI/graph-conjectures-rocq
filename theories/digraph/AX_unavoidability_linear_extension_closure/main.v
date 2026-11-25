(** * Linear unavoidability of the k-extensions of a linearly unavoidable family

Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, "Blow-ups and extensions of trees in
tournaments", 2024, arXiv:2410.23566, Conjecture 11 (2410.23566__05).

A digraph D is p-unavoidable if every tournament on p vertices contains D as a (not necessarily
induced) subdigraph.  The unavoidability unvd(D) is the least such p; it exists if and only if D is
acyclic.  A family F of digraphs is linearly unavoidable if there is a constant c such that
unvd(D) <= c|V(D)| for every D in F.  An acyclic digraph D is a k-extension of A if D - S = A for
some set S of k vertices.

Conjecture: for every integer k, if F is linearly unavoidable, then the family of the k-extensions
of the digraphs of F is linearly unavoidable.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]), and a family is a predicate [C] on them.  "unvd(D) = N" is the relation
[unavoidability_number D N].  Digraphs without unavoidability are ignored in [linearly_unavoidable],
which is harmless: a k-extension is acyclic, hence so is the digraph that it extends, and the
members of F that are not acyclic have no k-extension.  D - S = A is read up to isomorphism. *)

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

(** The unavoidability number is at most linear in the number of vertices in the class [C]
    (digraphs without unavoidability number are ignored). *)
Definition linearly_unavoidable (C : diGraph -> Prop) : Prop :=
  exists c : nat, forall (D : diGraph) (N : nat),
    C D -> unavoidability_number D N -> (N <= c * #|D|)%N.

(** The acyclic digraph [D] is a [k]-extension of [A]: the deletion of some [k] vertices gives
    [A]. *)
Definition k_extension (k : nat) (A D : diGraph) : Prop :=
  acyclic D /\ exists S : {set D}, #|S| = k /\ inhabited (induced (~: S) ≃ A).

(** ** Statement *)

Definition AX_unavoidability_linear_extension_closure : Prop :=
  forall (C : diGraph -> Prop) (k : nat),
    linearly_unavoidable C ->
    linearly_unavoidable (fun D => exists A : diGraph, C A /\ k_extension k A D).
