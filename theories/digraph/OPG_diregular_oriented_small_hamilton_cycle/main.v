(** * Hamilton cycles in small diregular oriented graphs

Jackson, "Long paths and cycles in oriented graphs", J. Graph Theory 5 (1981); Open Problem
Garden, hamilton_cycle_in_small_d_diregular_graphs.

An oriented graph is a digraph without loop and without digon.  It is d-diregular if every vertex
has in-degree d and out-degree d.

Conjecture: for d > 2, every d-diregular oriented graph on at most 4d + 1 vertices has a Hamilton
cycle.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  The degrees are equal to d: the conjecture is false for degrees at least d (two
regular tournaments on 2d + 1 vertices that share a vertex).  The digraph is nonempty.  A directed
cycle is given by the sequence of its vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** [D] is [d]-diregular: all in-degrees and out-degrees are equal to [d]. *)
Definition diregular (D : diGraph) (d : nat) : bool :=
  [forall v : D, (outdeg v == d) && (indeg v == d)].

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** [c] is a Hamiltonian directed cycle. *)
Definition hamiltonian_dicycle (D : diGraph) (c : seq D) : bool := dicycle c && (size c == #|D|).

(** ** Statement *)

Definition OPG_diregular_oriented_small_hamilton_cycle : Prop :=
  forall (D : diGraph) (d : nat), oriented D -> 0 < #|D| -> 2 < d ->
    diregular D d -> #|D| <= 4 * d + 1 ->
    exists c : seq D, hamiltonian_dicycle c.
