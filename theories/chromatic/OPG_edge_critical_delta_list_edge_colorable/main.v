(** * List colourings of edge-critical graphs

Mohar, "Problem of the Month"; Open Problem Garden, list_colorings_of_edge_critical_graphs.

A graph G of maximum degree Δ is Δ-edge-critical if it is not Δ-edge-colourable but every
edge-deleted subgraph is Δ-edge-colourable.

Conjecture: let G be a Δ-edge-critical graph, and let L(e) be a list of Δ colours for each edge e
of G.  Then G has a proper edge colouring from the lists L, unless all lists are equal.

Encoding.  Graphs are finite and simple.  Edge colourings of G are vertex colourings of its line
graph, in which deleting an edge of G amounts to deleting a vertex. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [Δ]-edge-critical (or edge-chromatic critical), for its maximum degree [Δ]: it is not
    [Δ]-edge-colourable, but it is after the deletion of any edge ([G] may be disconnected). *)
Definition Delta_edge_critical (G : sgraph) : Prop :=
  Delta G < χ([set: simple_line_graph G]) /\
  forall e : simple_line_graph G, χ([set: simple_line_graph G] :\ e) <= Delta G.

(** ** Statement *)

Definition OPG_edge_critical_delta_list_edge_colorable : Prop :=
  forall G : sgraph, Delta_edge_critical G ->
    forall (C : finType) (L : simple_line_graph G -> {set C}),
      (forall e, #|L e| = Delta G) ->
      (forall e e', L e = L e') \/ list_colorable L.
