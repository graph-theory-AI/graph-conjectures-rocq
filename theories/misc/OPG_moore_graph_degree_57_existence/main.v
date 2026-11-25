(** * Moore graph of degree 57

Hoffman, Singleton, "On Moore graphs with diameters 2 and 3", IBM J. Res. Develop. 4 (1960);
Open Problem Garden, 57_regular_moore_graph.

A Moore graph of diameter 2 is a graph with diameter 2 and girth 5 (the girth of a graph is the
length of its shortest cycles).

Question: does there exist a 57-regular graph with diameter 2 and girth 5?

The proposition states the positive answer. *)

From GraphTheory Require Import digraph sgraph.
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

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** The girth of [G] is [g]. *)
Definition girth (G : sgraph) (g : nat) : Prop :=
  girth_ge G g /\ (exists c : seq G, seq_cycle (--) c /\ size c = g).

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** [G] is connected of diameter [d] ([0 < d] is meant). *)
Definition diameter (G : sgraph) (d : nat) : Prop :=
  (forall u v : G, v \in ball d u) /\ (exists u v : G, v \notin ball d.-1 u).

(** ** Statement *)

Definition OPG_moore_graph_degree_57_existence : Prop :=
  exists G : sgraph, [/\ regular G 57, diameter G 2 & girth G 5].
