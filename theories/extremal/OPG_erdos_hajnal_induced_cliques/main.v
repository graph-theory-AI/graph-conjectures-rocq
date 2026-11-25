(** * The Erdős-Hajnal conjecture

Erdős, Hajnal, "Ramsey-type theorems", Discrete Appl. Math. 25 (1989); Open Problem Garden,
the_erdos_hajnal_conjecture.

Conjecture: for every graph H, there is a constant δ > 0 such that every graph G without induced
subgraph isomorphic to H has a clique or a stable set of size at least |V(G)|^δ.

Encoding.  The constant is δ = a/b with 0 < a <= b, which is not a restriction, and the inequality
m >= |V(G)|^δ is written |V(G)|^a <= m^b.  The graph G is nonempty (the conclusion is clear for the
empty graph). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Statement *)

Definition OPG_erdos_hajnal_induced_cliques : Prop :=
  forall H : sgraph, exists a b : nat, 0 < a /\ a <= b /\
    forall G : sgraph, 0 < #|G| -> induced_free G H ->
      #|G| ^ a <= maxn ω([set: G]) α([set: G]) ^ b.
