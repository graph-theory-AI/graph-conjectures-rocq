(** * Queue-number of graphs of bounded layered treewidth

Dujmović, Eppstein, Joret, Morin, Wood, "Minor-closed graph classes with bounded layered
pathwidth", arXiv:1810.08314, open problem (1810.08314__00).

A layering of G is a partition (V_0, V_1, ..., V_t) of V(G) such that each edge joins two vertices
of the same part or of consecutive parts.  The layered treewidth of G is the minimum l such that,
for some layering and some tree decomposition of G, each bag contains at most l vertices of each
part.  The queue-number of G is the minimum k such that, for some linear ordering of V(G), the
edges of G can be partitioned into k sets without nested edges, i.e. without edges ab and cd such
that a < c < d < b.

Open problem: do graphs of bounded layered treewidth have bounded queue-number?  The positive
answer is stated.

Encoding.  The bound on the queue-number is a function f of the bound on the layered treewidth.
A layering is a function from the vertices to nat, and a linear ordering is given by an injective
function to nat. *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/minor.v *)

(** [L] is a layering: adjacent vertices are in the same layer or in consecutive layers. *)
Definition layering (G : sgraph) (L : G -> nat) : Prop :=
  forall u v : G, u -- v -> (L u <= (L v).+1) /\ (L v <= (L u).+1).

(** The layered treewidth of [G] is at most [l]. *)
Definition layered_treewidth_le (G : sgraph) (l : nat) : Prop :=
  exists (L : G -> nat) (T : forest) (D : T -> {set G}),
    [/\ layering L, sdecomp T G D &
        forall (t : T) (i : nat), #|[set v in D t | L v == i]| <= l].

(** ** Definitions copied from GraphLib/topological.v *)

(** The queue number of [G] is at most [k]: for some linear order of the vertices, the edges can
    be given [k] colours so that no edge [c d] is nested inside an edge [a b] of the same
    colour. *)
Definition queue_number_le (G : sgraph) (k : nat) : Prop :=
  exists (ord : G -> nat) (q : {set G} -> nat),
    [/\ injective ord,
        (forall e : {set G}, e \in E(G) -> q e < k) &
        forall a b c d : G,
          a -- b -> c -- d -> q [set a; b] = q [set c; d] ->
          ord a < ord c -> ord c < ord d -> ord d < ord b -> False].

(** ** Statement *)

Definition AX_layered_treewidth_bounded_queue_number : Prop :=
  exists f : nat -> nat,
    forall (k : nat) (G : sgraph), layered_treewidth_le G k -> queue_number_le G (f k).
