(** * The Kelmans–Seymour conjecture

Seymour, Kelmans; Bondy, Murty, "Graph Theory", Appendix A, problem 29.

A subdivision of K_5 is a graph obtained from K_5 by replacing its edges by internally disjoint
paths.

Conjecture: every 5-connected non-planar graph contains a subdivision of K_5.

Encoding.  Graphs are finite and simple.  A graph is planar if it has no minor K_5 or K_{3,3}.  The
subdivision is a subgraph, not necessarily induced, given by its branch vertices and by the inner
vertices of the paths that replace the edges. *)

From GraphTheory Require Import digraph sgraph connectivity minor.
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

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition BM_kelmans_seymour_5_connected_nonplanar_k5_subdivision : Prop :=
  forall G : sgraph, 5.-connected G -> ~ planar G -> has_subdivision G 'K_5.
