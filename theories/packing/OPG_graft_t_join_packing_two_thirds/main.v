(** * Packing T-joins

DeVos; Open Problem Garden, packing_t_joins.

A graft consists of a graph G = (V,E) and a set T of vertices of even size.  A T-cut is an edge cut
δ(X) such that |X ∩ T| is odd.  A T-join is a set S of edges such that a vertex has odd degree in
(V,S) if and only if it is in T.  A T-join packing is a set of pairwise disjoint T-joins.

Conjecture: there exists a constant c (probably c = 1 suffices) such that every graft with minimum
T-cut size at least k contains a T-join packing of size at least (2/3)k - c.

Encoding.  Graphs are the finite multigraphs of GraphTheory, and the reference direction of the
edges plays no role.  Loops are allowed, and counted twice in the degrees.  The set T is nonempty:
otherwise there is no T-cut, hence no minimum T-cut size.  A packing is a list of T-joins such that
each edge is in at most one of them (they are distinct, as they are nonempty). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** ** Definitions copied from GraphLib/cycle.v *)

(** [J] is a [T]-join: the set of the vertices with odd degree in [J] is [T]. *)
Definition is_tjoin (G : mgraph) (T : {set G}) (J : {set edge G}) : Prop :=
  forall v : G, odd (mdeg_in J v) = (v \in T).

(** ** Statement *)

Definition OPG_graft_t_join_packing_two_thirds : Prop :=
  exists c : nat,
    forall (G : mgraph) (T : {set G}) (k : nat),
      T != set0 -> ~~ odd #|T| ->
      (forall S : {set G}, odd #|S :&: T| -> k <= #|mcut S|) ->
      exists Js : seq {set edge G},
        [/\ (forall J : {set edge G}, J \in Js -> is_tjoin T J),
            (forall e : edge G, count (fun J : {set edge G} => e \in J) Js <= 1)
          & 2 * k <= 3 * (size Js + c)].
