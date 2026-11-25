(** * Lines and bridges: finitely many exceptions without pendant edge

Aboulker, Matamala, Rochet, Zamora, "A new class of graphs that satisfies the Chen-Chvátal
conjecture", arXiv:1606.06011, Conjecture 2.2 (1606.06011__00).

Let G be a connected graph.  For vertices a, b, c of G, b is between a and c if
d(a,b) + d(b,c) = d(a,c).  The line through two distinct vertices a and b consists of a, b and
the vertices x such that one of a, b, x is between the two others.  Let ℓ(G) be the number of
distinct lines of G, and br(G) its number of bridges.  A pendant edge is an edge incident to a
vertex of degree 1.

Conjecture: there is a finite set F_0 of graphs such that every connected graph G not in F_0
has a pendant edge or satisfies ℓ(G) + br(G) >= |G|.

Encoding.  The finite set F_0 is replaced by a bound on the order of its graphs.  This is
equivalent, as there are finitely many graphs of bounded order up to isomorphism. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

(** [v] is on a shortest path from [u] to [w] ([G] is connected). *)
Definition metric_between (G : sgraph) (u v w : G) : bool :=
  graph_dist u v + graph_dist v w == graph_dist u w.

(** The line through [a] and [b] in the metric space of [G] (Chen and Chvatal): the vertices
    [x] such that one of [a], [b], [x] is between the two others. *)
Definition metric_line (G : sgraph) (a b : G) : {set G} :=
  [set x : G |
      metric_between a b x || metric_between a x b || metric_between x a b].

(** The number of lines of [G]. *)
Definition metric_line_count (G : sgraph) : nat :=
  #|[set L : {set G} |
      [exists a : G, [exists b : G, (a != b) && (L == metric_line a b)]]]|.

(** [e] is a bridge: an edge whose ends are in different components when it is deleted. *)
Definition bridge (G : sgraph) (e : {set G}) : bool :=
  (e \in E(G)) &&
  [exists x in e, exists y in e, ~~ connect (del_edges_rel e) x y].

(** The number of bridges of [G]. *)
Definition bridge_count (G : sgraph) : nat :=
  #|[set e : {set G} | bridge e]|.

(** ** Definitions specific to the conjecture *)

(** [ℓ(G) + br(G) >= |G|]. *)
Definition metric_lines_bridges_bound (G : sgraph) : Prop :=
  #|G| <= metric_line_count G + bridge_count G.

(** [G] has a pendant edge. *)
Definition has_pendant_edge (G : sgraph) : Prop :=
  exists v : G, #|N(v)| = 1.

(** ** Statement *)

Definition AX_chen_chvatal_lines_bridges_finite_exceptions : Prop :=
  exists exceptional_order_bound : nat,
    forall G : sgraph,
      connected [set: G] ->
      exceptional_order_bound < #|G| ->
      has_pendant_edge G \/ metric_lines_bridges_bound G.
