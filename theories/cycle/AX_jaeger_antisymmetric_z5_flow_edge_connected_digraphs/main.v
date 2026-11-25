(** * Antisymmetric variant of Jaeger's weak 3-flow conjecture

Esperet, de Joannis de Verclos, Le, Thomassé, "Additive bases and flows in graphs", SIAM
Journal on Discrete Mathematics 32 (2018), arXiv:1701.03366 (1701.03366__00).

A directed graph is k-edge-connected if its underlying undirected graph is.  For an abelian group
B, a B-flow in a directed graph is a map f from the arcs to B such that, at every vertex, the sum
of the values on outgoing arcs equals the sum on incoming arcs.  It is antisymmetric if no two
arcs, equal or not, receive mutually inverse elements of B.  In particular, no arc gets 0.

Conjecture: there is a constant k such that every directed k-edge-connected graph has a
Z_5-antisymmetric flow.

Encoding.  Directed graphs are multigraphs with the direction of the edges from source to target.
Loops are allowed, unlike in the source, which changes nothing: a loop does not matter for the
flow condition, and can be given the value of an arc that is not a loop, or 1 if there is none.
Elements of Z_5 are natural numbers less than 5, added modulo 5. *)

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

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

(** ** Definitions specific to the conjecture *)

(** [G] has a Z_5-antisymmetric flow. *)
Definition z5_antisymmetric_flow (G : mgraph) : Prop :=
  exists phi : edge G -> 'I_5,
    [/\ forall e : edge G, phi e != ord0,
        forall e e' : edge G, (val (phi e) + val (phi e')) %% 5 != 0
      & forall v : G,
          ((\sum_(e : edge G | source e == v) val (phi e)) %% 5 =
           (\sum_(e : edge G | target e == v) val (phi e)) %% 5)].

(** ** Statement *)

Definition AX_jaeger_antisymmetric_z5_flow_edge_connected_digraphs : Prop :=
  exists k : nat,
    forall G : mgraph,
      medge_connected G k ->
      z5_antisymmetric_flow G.
