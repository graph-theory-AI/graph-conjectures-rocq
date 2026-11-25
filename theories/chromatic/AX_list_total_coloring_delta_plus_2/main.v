(** * The list version of the total colouring conjecture

Bonamy, Pierron, Sopena, "Every planar graph with Δ >= 8 is totally (Δ+2)-choosable",
arXiv:1904.12060, Conjecture 5 (1904.12060__00).

A total colouring of a graph G is an assignment of colours to the vertices and the edges of G such
that any two adjacent vertices, any two edges with a common end, and any vertex and incident edge
receive different colours.  G is totally k-choosable if for every assignment of lists of k colours
to its vertices and edges, G has a total colouring from these lists.  The list total chromatic
number χ''_l(G) is the minimum such k.  Δ(G) is the maximum degree of G.

Conjecture 5: every simple graph G satisfies χ''_l(G) <= Δ(G) + 2.

Encoding.  Graphs are finite and simple.  The total colourings of G are the proper vertex colourings
of its total graph.  The lists have at least (instead of exactly) Δ(G) + 2 colours, which is
equivalent. *)

From GraphTheory Require Import digraph sgraph.
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

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

Section TotalGraph.
Variable G : sgraph.

(** Adjacent vertices, distinct edges with a common end, or an edge and one of its ends. *)
Definition total_graph_rel : rel (G + simple_line_graph G)%type :=
  fun a b =>
    match a, b with
    | inl x, inl y => x -- y
    | inr e, inr f => e -- f
    | inl x, inr e => x \in val e
    | inr e, inl x => x \in val e
    end.

Lemma total_graph_sym : symmetric total_graph_rel.
Proof. by move=> [x|e] [y|f] //=; rewrite sg_sym. Qed.

Lemma total_graph_irrefl : irreflexive total_graph_rel.
Proof. by move=> [x|e] //=; rewrite sg_irrefl. Qed.

(** The total graph of [G], whose proper colourings are the total colourings of [G]. *)
Definition total_graph : sgraph := SGraph total_graph_sym total_graph_irrefl.

End TotalGraph.

(** ** Statement *)

Definition AX_list_total_coloring_delta_plus_2 : Prop :=
  forall G : sgraph, choosable (total_graph G) (Delta G + 2).
