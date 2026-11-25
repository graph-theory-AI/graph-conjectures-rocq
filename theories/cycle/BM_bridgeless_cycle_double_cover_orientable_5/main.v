(** * The orientable five cycle double cover conjecture

Archdeacon (1984), Jaeger (1988); Bondy, Murty, "Graph Theory", Appendix A, problem 26.

An even subgraph of a graph G is a spanning subgraph whose degrees are all even.  A double cover of
G by even subgraphs is a list of even subgraphs such that every edge of G is in exactly two of them.
It is orientable if its members can be decomposed into cycles, and these cycles oriented as
directed cycles, such that every edge is traversed once in each direction.

Conjecture: every 2-edge-connected graph has an orientable double cover by five even subgraphs.

Encoding.  Graphs are the finite multigraphs of GraphTheory, with at least one vertex: loops and
parallel edges are allowed, and loops are counted twice in the degrees.  2-edge-connected means
connected and bridgeless.  Even subgraphs are sets of edges, possibly empty or repeated in the
double cover.  Orienting the cycles of a decomposition of an even subgraph amounts to orienting its
edges such that the in-degree of each vertex is equal to its out-degree.  An orientation tells
whether each edge keeps its reference direction, from its source to its target. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph.
From GraphTheory Require skeleton.
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

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

(** ** Definitions copied from GraphLib/cycle.v *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types C : {set edge G}.

(** [C] is an even subgraph: all its degrees are even. *)
Definition even_subgraph C : Prop :=
  forall v : G, ~~ odd (mdeg_in C v).

End EdgeSets.

(** The tail of [e]. *)
Definition orient_tail (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then source e else target e.

(** The head of [e]. *)
Definition orient_head (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then target e else source e.

(** [o] is a balanced orientation of [C]: in-degrees and out-degrees are equal. *)
Definition balanced_orientation (G : mgraph) (C : {set edge G}) (o : edge G -> bool) : Prop :=
  forall v : G,
    #|[set e in C | orient_tail o e == v]| = #|[set e in C | orient_head o e == v]|.

(** [G] has an orientable [k]-cycle double cover: [k] even subgraphs with balanced orientations,
    such that each edge is in exactly two of them, with opposite directions. *)
Definition orientable_cycle_cover (G : mgraph) (k : nat) : Prop :=
  exists (C : 'I_k -> {set edge G}) (d : 'I_k -> edge G -> bool),
    [/\ (forall i : 'I_k, even_subgraph (C i)),
        (forall i : 'I_k, balanced_orientation (C i) (d i)),
        (forall e : edge G, #|[set i : 'I_k | e \in C i]| = 2)
      & (forall (e : edge G) (i j : 'I_k),
           i != j -> e \in C i -> e \in C j -> d i e != d j e)].

(** ** Statement *)

Definition BM_bridgeless_cycle_double_cover_orientable_5 : Prop :=
  forall G : mgraph,
    0 < #|G| -> medge_connected G 2 -> orientable_cycle_cover G 5.
