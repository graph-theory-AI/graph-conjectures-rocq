(** * The list edge colouring conjecture

Attributed to Vizing, Gupta, Albertson and Collins, Bollobás and Harris (Jensen and Toft, "Graph
Coloring Problems", 1995, Problem 12.20); Open Problem Garden, edge_list_coloring_conjecture.

The edge chromatic number of a multigraph G is the minimum k such that the edges of G have a proper
colouring with k colours (distinct edges with a common end have different colours).  The list edge
chromatic number of G is the minimum k such that the edges of G have a proper colouring from all
lists of at least k colours.

Conjecture: the edge chromatic number of a loopless multigraph G is equal to its list edge
chromatic number.

Encoding.  Multigraphs are finite and may have parallel edges.  Edge colourings of G are vertex
colourings of its line graph.  "The list chromatic number is m" is a relation. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

Lemma mline_rel_sym (G : mgraph) : symmetric (@mline_rel G).
Proof.
move=> e1 e2; rewrite /mline_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.

Lemma mline_rel_irrefl (G : mgraph) : irreflexive (@mline_rel G).
Proof. by move=> e; rewrite /mline_rel eqxx. Qed.

(** The line graph of the multigraph [G] (parallel edges are adjacent). *)
Definition mline_graph (G : mgraph) : sgraph := SGraph (@mline_rel_sym G) (@mline_rel_irrefl G).

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

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** ** Statement *)

Definition OPG_list_edge_chromatic_equals_edge_chromatic : Prop :=
  forall (G : mgraph) (m : nat),
    mloopless G ->
    choice_number (mline_graph G) m ->
    m = χ([set: mline_graph G]).
