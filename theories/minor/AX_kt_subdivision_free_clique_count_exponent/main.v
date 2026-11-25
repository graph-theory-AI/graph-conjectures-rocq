(** * Number of cliques in graphs without K_t subdivision

Fox, Wei, "On the number of cliques in graphs with a forbidden subdivision or immersion",
arXiv:1606.06810, conjecture (1606.06810__01).

Conjecture: the maximum number of cliques in a graph on n vertices with no K_t subdivision is
3^(2t/3 + o(t)) n.

The cliques are all the complete subgraphs, including the empty one.

Encoding.  Graphs are finite, simple and nonempty (the bound would be 0 for n = 0, but the empty
clique is counted).  The term o(t) is expressed as follows: for every positive rational ε = a/b and
every sufficiently large t, all graphs without K_t subdivision on n vertices have at most 3^(2t/3 +
ε t) n cliques, and one of them has at least 3^(2t/3 - ε t) n cliques when n is sufficiently large
in terms of t.  The latter condition on n is necessary, as a graph with n <= t vertices has at most
2^t cliques.  Both sides of the inequalities are raised to the power 3b, and the factor 3^(-ε t) of
the second one is moved to the other side. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

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

Definition AX_kt_subdivision_free_clique_count_exponent : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    eventually (fun t =>
      (forall G : sgraph,
         0 < #|G| ->
         ~ has_subdivision G 'K_t ->
         #|cliques [set: G]| ^ (3 * b) <= 3 ^ ((2 * b + 3 * a) * t) * #|G| ^ (3 * b)) /\
      eventually (fun n =>
        exists G : sgraph,
          [/\ #|G| = n,
              ~ has_subdivision G 'K_t
            & 3 ^ (2 * b * t) * n ^ (3 * b) <=
              3 ^ (3 * a * t) * #|cliques [set: G]| ^ (3 * b)])).
