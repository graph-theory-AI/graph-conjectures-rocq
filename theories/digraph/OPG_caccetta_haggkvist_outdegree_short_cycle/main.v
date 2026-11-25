(** * Caccetta–Häggkvist conjecture

Caccetta, Häggkvist, "On minimal digraphs with given girth", Congressus Numerantium 21 (1978);
Open Problem Garden, caccetta_haggkvist_conjecture.

Conjecture: every simple digraph of order n with minimum out-degree at least r has a directed cycle
of length at most ⌈n/r⌉.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], without loop here.  Digons are allowed, and are directed cycles of length two.  The
digraph is nonempty and r is positive, which is implicit in the source.  The ceiling ⌈n/r⌉ is the
integer quotient of n + r - 1 by r.  A directed cycle is given by the sequence of its vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** ** Statement *)

Definition OPG_caccetta_haggkvist_outdegree_short_cycle : Prop :=
  forall (D : diGraph) (r : nat),
    0 < #|D| -> irreflexive (@edge_rel D) -> 0 < r -> min_outdeg_ge D r ->
    exists c : seq D, dicycle c /\ size c <= (#|D| + r - 1) %/ r.
