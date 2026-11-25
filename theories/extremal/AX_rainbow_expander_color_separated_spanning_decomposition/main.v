(** * Decomposing an edge-coloured expander into two connected subgraphs

Alon, Bucić, Sauermann, Zakharov, Zamir, "Essentially tight bounds for rainbow cycles in proper
edge-colourings", arXiv:2309.04460, Question 10.2 (2309.04460__01).

Let d(G) denote the average degree of G.  A graph G on n vertices is a robust sublinear expander
if for every ε with 0 <= ε <= 1, every nonempty set U of at most n^(1-ε) vertices and every set F
of at most (ε/3) d(G) |U| edges, there are at least (ε/3)|U| vertices outside U that are adjacent
to U in G - F.

Question 10.2: does there exist a constant C > 0 such that the edges of any properly edge-coloured
robust sublinear expander G on n vertices with d(G) >= C log n can be decomposed into two spanning
connected subgraphs in such a way that every colour appears on only one of them?  The proposition
states a positive answer.

Encoding.  ε is a rational number a/b, which is equivalent: for fixed U and F, the ε to consider
form an interval whose lower bound is rational and belongs to it.  The inequalities are multiplied
by the denominators, with d(G) = 2|E(G)|/n, and raised to the power b for |U| <= n^(1-ε).  The
inequality d(G) >= C log n becomes d(G) >= C ⌊log_2 n⌋, which is equivalent up to a change of the
constant C.  The decomposition is given by a set of colours: it consists of the edges with a
colour in this set, and of the other edges. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices outside [U] with a neighbour in [U]. *)
Definition external_neigh (G : sgraph) (U : {set G}) : {set G} := NS(U) :\: U.

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

(** The edges of [G] that are not in [F]. *)
Definition del_edge_set_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_edge_set_sym : symmetric del_edge_set_rel.
Proof. by move=> x y; rewrite /del_edge_set_rel /= sg_sym setUC. Qed.

Lemma del_edge_set_irrefl : irreflexive del_edge_set_rel.
Proof. by move=> x; rewrite /del_edge_set_rel /= sg_irrefl. Qed.

(** [G] without the edges of [F]. *)
Definition del_edge_set : sgraph := SGraph del_edge_set_sym del_edge_set_irrefl.

End DelEdgeSet.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** ** Definitions specific to the conjecture *)

(** [G] is a robust sublinear expander. *)
Definition robust_sublinear_expander (G : sgraph) : Prop :=
  forall (a b : nat) (U : {set G}) (F : {set {set G}}),
    0 < b -> a <= b ->
    0 < #|U| ->
    #|U| ^ b <= #|G| ^ (b - a) ->
    F \subset E(G) ->
    3 * b * (#|G| * #|F|) <= 2 * a * (#|E(G)| * #|U|) ->
    a * #|U| <= 3 * b * #|@external_neigh (del_edge_set F) U|.

(** ** Statement *)

Definition AX_rainbow_expander_color_separated_spanning_decomposition : Prop :=
  exists C : nat,
    0 < C /\
    forall (G : sgraph) (Col : finType) (col : {set G} -> Col),
      robust_sublinear_expander G ->
      proper_edge_coloring col ->
      (forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|) ->
      exists P : pred Col,
        connected [set: edge_color_class col P] /\
        connected [set: edge_color_class col (predC P)].
