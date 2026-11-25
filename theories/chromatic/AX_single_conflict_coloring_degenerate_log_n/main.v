(** * Single-conflict chromatic number of degenerate graphs

Dvořák, Esperet, Kang, Ozeki, "Single-conflict colouring", arXiv:1803.10962 (1803.10962__01).

The single-conflict chromatic number of G is the minimum k >= 1 such that, whenever a pair of
colours of [k] (a conflict) is given for each edge of G, one colour for each end, there is a
colouring of the vertices of G with k colours, not necessarily proper, such that no edge has the
colours of its conflict.  A graph is d-degenerate if each of its nonempty subgraphs has a vertex of
degree at most d.

Conjecture: there is a constant C > 0 such that the single-conflict chromatic number of every
d-degenerate graph on n vertices is at most C √d log n.

Encoding.  Graphs are simple.  At most one conflict is given for each edge, which is equivalent.  As
the property is monotone in k, the upper bound means that it holds for every k >= 1 such that
k >= C √d ⌊log_2 n⌋; this inequality is squared, and the base and the floor only change the
constant, which is a natural number.  If d = 0 or n <= 1, where this bound is 0, the graph has no
edge and the statement only says that one colour suffices. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] has a colouring with [k] colours that avoids the conflicts [C]. *)
Definition conflict_colorable
    (G : sgraph) (k : nat) (C : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  exists col : G -> 'I_k,
    forall u v : G, u -- v -> ~~ C u v (col u) (col v).

(** ** Definitions specific to the conjecture *)

(** [F] gives at most one conflict for each edge. *)
Definition single_conflict_assignment
    (G : sgraph) (k : nat) (F : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v -> forall a b : 'I_k, F u v a b = F v u b a) /\
  (forall u v : G, u -- v -> #|[set ab : 'I_k * 'I_k | F u v ab.1 ab.2]| <= 1).

(** Every assignment of at most one conflict to each edge is avoided by a colouring with [k]
    colours: for [0 < k], the single-conflict chromatic number of [G] is at most [k]. *)
Definition single_conflict_colorable (G : sgraph) (k : nat) : Prop :=
  forall F : G -> G -> 'I_k -> 'I_k -> bool,
    single_conflict_assignment F -> conflict_colorable F.

(** ** Statement *)

Definition AX_single_conflict_coloring_degenerate_log_n : Prop :=
  exists C : nat,
    forall (G : sgraph) (d k : nat), 0 < k -> degenerate G d ->
      C ^ 2 * d * trunc_log 2 #|G| ^ 2 <= k ^ 2 ->
      single_conflict_colorable G k.
