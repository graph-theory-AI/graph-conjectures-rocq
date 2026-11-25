(** * Treewidth of (C_4, diamond, theta, prism, even wheel, K_t)-free graphs

Abrishami, Chudnovsky, Hajebi, Spirkl, "Induced subgraphs and tree decompositions IV. (Even hole,
diamond, pyramid)-free graphs", Electron. J. Combin. 30 (2023), arXiv:2203.06775, Conjecture 1.6
(2203.06775__00).

A graph is free of a family of graphs if it has no induced subgraph isomorphic to a member of the
family.  A hole is an induced cycle of length at least 4.  The diamond is K_4 minus an edge.  A
theta consists of two nonadjacent vertices a and b and three paths of length at least 2 from a to b
whose interiors are disjoint and anticomplete.  A prism consists of two disjoint triangles
a_1 a_2 a_3 and b_1 b_2 b_3 and three paths P_i from a_i to b_i such that the only edges between
distinct P_i and P_j are a_i a_j and b_i b_j.  A wheel (H,w) consists of a hole H and a vertex w
with at least three pairwise nonadjacent neighbours in H.  A line wheel consists of a hole H and a
vertex outside H whose neighbours in H form two disjoint edges.  An even wheel is a line wheel, or
a wheel (H,w) where w has an even number of neighbours in H.

Conjecture 1.6: for every t > 0, there exists c_t such that every (C_4, diamond, theta, prism, even
wheel, K_t)-free graph has treewidth at most c_t.

Encoding.  Graphs are finite and simple.  A theta is a subdivision of K_{2,3}, and a prism is a
subdivision of the prism on 6 vertices where the edges of the triangles are not subdivided.  An
even wheel is a hole and a vertex outside it with an even number, at least 3, of neighbours in the
hole; this is equivalent for diamond-free graphs, as the neighbours of the vertex in the hole
contain three pairwise nonadjacent vertices, or form two disjoint edges, or are four consecutive
vertices of the hole, which gives a diamond.  A graph is K_t-free if its clique number is less than
t.  The case t = 0 is included, where the statement is vacuous. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring treewidth.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

Section Sequences.
Variable T : finType.
Implicit Types s c : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

End Sequences.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (c : seq G) (u v : G).

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

(** [c] is a hole: an induced cycle of length at least 4. *)
Definition hole c : Prop := chordless_cycle c /\ 3 < size c.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** The diamond: [K_4] minus an edge. *)
Definition diamond : sgraph := del_edges ([set ord0; ord_max] : {set 'K_4}).

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

End Products.

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

Section SubdivisionOf.
Variables (K H : sgraph) (m : subdivision_model K H).

(** [x] is a vertex of the subdivision. *)
Definition subdiv_vertex (x : H) : Prop :=
  (exists h : K, subdiv_branch m h = x) \/ (exists u v : K, u -- v /\ x \in subdiv_path m u v).

(** [x y] is an edge of the subdivision. *)
Definition subdiv_edge (x y : H) : Prop :=
  exists u v : K, u -- v /\
    [set x; y] \in
      seq_edge_list (subdiv_branch m u :: rcons (subdiv_path m u v) (subdiv_branch m v)).

(** The subdivision has all the vertices and edges of [H]. *)
Definition subdiv_spans : Prop :=
  (forall x : H, subdiv_vertex x) /\ (forall x y : H, x -- y -> subdiv_edge x y).

End SubdivisionOf.

(** [H] is a subdivision of [K]. *)
Definition is_subdivision_of (H K : sgraph) : Prop :=
  exists m : subdivision_model K H, subdiv_spans m.

(** [H] is a theta: a subdivision of [K_2,3]. *)
Definition is_theta (H : sgraph) : Prop := is_subdivision_of H (KB 2 3).

(** [H] is a prism, in the sense of three-path configurations: a subdivision of the prism on 6
    vertices (two triangles joined by three edges), where the edges of the triangles are not
    subdivided. *)
Definition prism_subdivision (H : sgraph) : Prop :=
  exists m : subdivision_model (cartesian_product 'K_3 'K_2) H,
    subdiv_spans m /\
    forall (u v : cartesian_product 'K_3 'K_2),
      u -- v -> u.2 == v.2 -> subdiv_path m u v = [::].

(** [G] has no even wheel: no vertex outside a hole has an even number, at least 3, of
    neighbours in the hole. *)
Definition even_wheel_free (G : sgraph) : Prop :=
  forall (v : G) (c : seq G),
    hole c -> v \notin c -> 3 <= #|N(v) :&: [set:: c]| -> odd #|N(v) :&: [set:: c]|.

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Statement *)

Definition AX_c4_diamond_theta_prism_bounded_treewidth : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G diamond ->
      (forall H : sgraph, is_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, prism_subdivision H -> ~ has_induced_copy G H) ->
      even_wheel_free G ->
      ω([set: G]) < t ->
      treewidth_le G c.
