(** * Logarithmic treewidth without the four basic obstructions

Abrishami, Chudnovsky, Hajebi, Spirkl, "Induced subgraphs and tree decompositions III.
Three-path-configurations and logarithmic treewidth", arXiv:2109.01310, Conjecture 1.10
(2109.01310__00).

tw(G) is the treewidth of G.  The wall W_{t×t} is the planar graph of maximum degree three
obtained from the t×t grid by deleting every other vertical edge.  The line graph of F has vertex
set E(F), two edges being adjacent when they share an end.

Conjecture 1.10: for all t >= 0 there exists c such that every graph G with no K_t, no K_{t,t}, no
subdivision of W_{t×t} and no line graph of a subdivision of W_{t×t} as induced subgraphs
satisfies tw(G) <= c log |V(G)|.

Encoding.  The logarithm is in base 2, rounded down, and increased by 1 so as to absorb the
rounding; this only changes the constant c.  The source does not fix the dimensions of the wall;
here it has t rows and t columns.  Other conventions give an equivalent conjecture, as t is
arbitrary and a subdivision of a large wall contains an induced subdivision of a smaller one.
"W is a subdivision of K" ([is_subdivision_of W K]) means that W has a model of K, with branch
vertices and paths, that uses all its vertices and edges; subdividing no edge is allowed. *)

From GraphTheory Require Import preliminaries digraph sgraph treewidth.
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
Implicit Types s : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

End Sequences.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

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

(** The edges of the wall, in one direction: those of the rows of the grid, and every other edge
    of its columns. *)
Definition wall_rel (t : nat) (u v : 'I_t * 'I_t) : bool :=
  ((u.1 == v.1) && ((u.2 : nat).+1 == v.2)) ||
  [&& (u.2 : nat) == v.2, (u.1 : nat).+1 == v.1 & ~~ odd ((u.1 : nat) + u.2)].

(** The wall obtained from the grid with [t] rows and [t] columns. *)
Definition wall (t : nat) : sgraph := sgraph_of_rel (@wall_rel t).

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** ** Statement *)

Definition AX_four_families_free_logarithmic_treewidth : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G 'K_t ->
      ~ has_induced_copy G (KB t t) ->
      (forall W : sgraph, is_subdivision_of W (wall t) -> ~ has_induced_copy G W) ->
      (forall W : sgraph, is_subdivision_of W (wall t) ->
         ~ has_induced_copy G (simple_line_graph W)) ->
      treewidth_le G (c * (trunc_log 2 #|G|).+1).
