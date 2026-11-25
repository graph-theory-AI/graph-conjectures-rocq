(** * 4-holes in controlled triangle-free graphs

Scott, Seymour, "Induced subgraphs of graphs with large chromatic number. IV. Consecutive holes",
J. Combin. Theory B 132 (2018), arXiv:1509.06563, question on 2.1 (1509.06563__03).

A hole is an induced cycle of length at least 4, and an l-hole is a hole of length l.  For a graph
H, let χ²(H) be the maximum, over the vertices v of H, of the chromatic number of the subgraph of H
induced by the vertices at distance at most 2 from v.  For a non-decreasing function φ from natural
numbers to natural numbers, a graph G is (2,φ)-controlled if χ(H) <= φ(χ²(H)) for every induced
subgraph H of G.

Question: let φ be a non-decreasing function; does there exist n such that every (2,φ)-controlled
triangle-free graph with chromatic number more than n has a 4-hole?

The proposition states the positive answer, for every φ.

Encoding.  Graphs are finite and simple.  A 4-hole is a cycle of length 4, which is necessarily
induced in a triangle-free graph. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** ** Definitions specific to the conjecture *)

(** The maximum chromatic number of a ball of radius 2 of [G]. *)
Definition local_chromatic_radius_two (G : sgraph) : nat :=
  \max_(v : G) χ([set: induced (ball 2 v)]).

(** [G] is [(2,phi)]-controlled. *)
Definition two_controlled (G : sgraph) (phi : nat -> nat) : Prop :=
  forall S : {set G},
    χ([set: induced S]) <= phi (local_chromatic_radius_two (induced S)).

(** [G] has a 4-hole ([G] is triangle-free). *)
Definition has_4_hole (G : sgraph) : Prop := exists c : seq G, ucycle (--) c /\ size c = 4.

(** ** Statement *)

Definition AX_controlled_triangle_free_chromatic_4_hole : Prop :=
  forall phi : nat -> nat, {homo phi : x y / x <= y} ->
    exists n : nat, forall G : sgraph,
      triangle_free G -> two_controlled G phi -> n < χ([set: G]) -> has_4_hole G.
