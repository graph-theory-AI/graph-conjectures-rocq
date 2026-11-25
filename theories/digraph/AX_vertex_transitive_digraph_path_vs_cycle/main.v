(** * Longest paths and longest cycles in vertex transitive digraphs

Bucić, Hendrey, Mohar, Steiner, Yepremyan, "Long cycles in vertex transitive digraphs", 2026,
arXiv:2602.16333, Question 4.4 (2602.16333__03).

A digraph is vertex transitive if its automorphism group acts transitively on its vertices.  Paths
and cycles are directed.

Question: is there C > 0 such that, in any vertex transitive digraph, the length of a longest path
is at most C times the length of a longest directed cycle?  The proposition states the positive
answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Lengths are numbers of arcs, and C is an integer.  For every path of positive
length there is a directed cycle that is long enough (digraphs without arc, which have no directed
cycle, are thus excluded).  Loops are allowed, which is harmless: a vertex transitive digraph has
loops on all its vertices or on none, and, if it has a path of positive length, a directed cycle of
length at least 2. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** [D] is vertex-transitive. *)
Definition vertex_transitive (D : diGraph) : bool :=
  [forall u : D, [forall v : D, [exists p : {perm D}, (p \in automorphisms D) && (p u == v)]]].

(** ** Statement *)

Definition AX_vertex_transitive_digraph_path_vs_cycle : Prop :=
  exists C : nat, forall D : diGraph, vertex_transitive D ->
    forall (x : D) (s : seq D), dipath x s -> 0 < size s ->
      exists c : seq D, dicycle c /\ size s <= C * size c.
