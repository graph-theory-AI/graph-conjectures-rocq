(** * Bondy's linear-length cycle conjecture for cyclically 4-edge-connected cubic graphs

Bondy, see Fleischner and Jackson (1989); Bondy, Murty, "Graph Theory", Appendix A, problem 65.

A graph is cubic if all degrees are 3.  It is cyclically k-edge-connected if it has no edge cut
with fewer than k edges whose deletion leaves two components that each contain a cycle.

Conjecture: there is a positive constant c such that every 3-connected, cyclically
4-edge-connected cubic graph on n vertices contains a cycle of length at least cn.

Encoding.  Graphs are simple.  The constant is a rational number p/q, without loss of generality.
Cyclic 4-edge-connectivity is expressed with the cuts between S and V \ S such that neither S nor
V \ S induces a forest, which is equivalent. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The edges with exactly one end in [S]. *)
Definition cut_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | (e :&: S != set0) && (e :&: (~: S) != set0)].

(** ** Definitions copied from GraphLib/cycle.v *)

(** [G] is cyclically [k]-edge-connected: each cut with cycles on both sides has at least [k]
    edges. *)
Definition cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    ~ is_forest S -> ~ is_forest (~: S) -> k <= #|cut_edges S|.

(** ** Statement *)

Definition BM_bondy_cubic_cyclically_4_connected_long_cycle : Prop :=
  exists p q : nat,
    [/\ 0 < p, 0 < q &
        forall G : sgraph,
          regular G 3 -> 3.-connected G -> cyclically_edge_connected G 4 ->
          exists c : seq G, seq_cycle (--) c /\ p * #|G| <= q * size c].
