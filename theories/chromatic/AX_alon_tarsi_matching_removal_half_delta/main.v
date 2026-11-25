(** * Alon-Tarsi number after removal of a matching

Bradshaw, Chen, Ma, Mohar, Wu, "List-avoiding orientations", arXiv:2209.09107, Question 6.2
(2209.09107__01).

For an orientation D of a graph G, a spanning subgraph is Eulerian if every vertex has equal
indegree and outdegree in it.  D is an Alon-Tarsi orientation if the number of Eulerian subgraphs
with an even number of edges differs from the number of those with an odd number of edges.  The
Alon-Tarsi number AT(G) is the minimum k such that G has an Alon-Tarsi orientation of maximum
outdegree less than k.

Question 6.2: does there exist a constant C such that every graph G of maximum degree Δ has a
matching M such that AT(G - M) <= Δ/2 + C?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  An orientation is a set of pairs of vertices.  The
constant C is a natural number, without loss of generality.  The inequality is stated as the
existence of an integer k such that AT(G - M) <= k and 2k <= Δ + 2C. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

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

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Each vertex has as many in-neighbours as out-neighbours (such a digraph is also called
    eulerian, connected or not). *)
Definition balanced_digraph (D : diGraph) : bool := [forall v : D, indeg v == outdeg v].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The Eulerian subsets of the arc set [A]: indegrees and outdegrees are equal. *)
Definition eulerian_subsets (V : finType) (A : {set V * V}) : {set {set V * V}} :=
  [set B : {set V * V} | (B \subset A) && balanced_digraph (digraph_of_arcs B)].

(** [A] is an Alon-Tarsi orientation: it has not the same numbers of Eulerian subsets with an
    even number of arcs and with an odd number of arcs. *)
Definition alon_tarsi (V : finType) (A : {set V * V}) : bool :=
  #|[set B in eulerian_subsets A | ~~ odd #|B|]| != #|[set B in eulerian_subsets A | odd #|B|]|.

(** The Alon-Tarsi number of [G] is at most [k]: [G] has an Alon-Tarsi orientation with
    outdegrees less than [k]. *)
Definition alon_tarsi_number_le (G : sgraph) (k : nat) : Prop :=
  exists A : {set G * G},
    [/\ forall x y : G, (x, y) \in A -> x -- y,
        forall x y : G, x -- y -> ((x, y) \in A) (+) ((y, x) \in A),
        alon_tarsi A &
        forall v : G, (outdeg (D := digraph_of_arcs A) v).+1 <= k].

(** ** Statement *)

Definition AX_alon_tarsi_matching_removal_half_delta : Prop :=
  exists C : nat, forall G : sgraph, exists M : {set {set G}},
    matching M /\
    exists k : nat, 2 * k <= Delta G + 2 * C /\ alon_tarsi_number_le (del_edge_set M) k.
