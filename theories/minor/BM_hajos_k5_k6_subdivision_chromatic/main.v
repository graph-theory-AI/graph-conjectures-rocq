(** * Hajós' conjecture for k = 5 and k = 6

Hajós, Catlin; Bondy, Murty, "Graph Theory", Appendix A, problem 42.

A graph is k-chromatic if its chromatic number is k.

Question: does every k-chromatic graph contain a subdivision of K_k when k = 5 and when k = 6?

The proposition states the positive answer, for both values of k.

Encoding.  Graphs are finite and simple.  The subdivision is a subgraph, not necessarily induced,
given by its branch vertices and by the inner vertices of the paths that replace the edges. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/minor.v *)

(** Subdivisions of [H] in [G]: distinct branch vertices and, for each edge of [H], the list of
    the inner vertices of a path between its branch vertices (reversed for the opposite
    direction).  Inner vertices are not branch vertices, and the paths of distinct edges have no
    common inner vertex. *)
Record subdivision_model (H G : sgraph) := SubdivisionModel {
  subdiv_branch : H -> G;
  subdiv_branch_inj : injective subdiv_branch;
  subdiv_path : H -> H -> seq G;
  subdiv_pathP : forall u v : H, u -- v ->
      upath (subdiv_branch u) (subdiv_branch v) (rcons (subdiv_path u v) (subdiv_branch v));
  subdiv_pathC : forall u v : H, u -- v -> subdiv_path v u = rev (subdiv_path u v);
  subdiv_path_branch : forall (u v w : H) (x : G),
      u -- v -> x \in subdiv_path u v -> x != subdiv_branch w;
  subdiv_path_disjoint : forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' -> x \in subdiv_path u v -> x \in subdiv_path u' v' ->
      [set u; v] = [set u'; v']
}.

(** [G] contains a subdivision of [H] ([H] is a topological minor of [G]). *)
Definition has_subdivision (G H : sgraph) : Prop := inhabited (subdivision_model H G).

(** ** Statement *)

Definition BM_hajos_k5_k6_subdivision_chromatic : Prop :=
  forall (k : nat) (G : sgraph),
    (k = 5) \/ (k = 6) -> χ([set: G]) = k -> has_subdivision G 'K_k.
