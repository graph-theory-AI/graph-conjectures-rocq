(** * Pure pairs in blockades without transversal triangle

Scott, Seymour, Spirkl, "Pure pairs. IX. Transversal trees", arXiv:2111.00532, Question 1.3
(2111.00532__00).

A pure pair is a pair X, Y of disjoint sets of vertices that are complete (every vertex of X is
adjacent to every vertex of Y) or anticomplete (no edge between X and Y).  A blockade of length 3
in a graph G is a triple B = (B_1, B_2, B_3) of pairwise disjoint nonempty sets of vertices.  Its
width W is the minimum size of B_1, B_2, B_3.  A B-transversal triangle is a triangle with exactly
one vertex in each B_i.

Question: do there exist c, ε > 0 such that, for every blockade B = (B_1, B_2, B_3) of width W in a
graph G without B-transversal triangle, there are distinct i, j ∈ {1, 2, 3} and a pure pair
X ⊆ B_i, Y ⊆ B_j with |X| >= ε W and |Y| >= ε W^c?

The proposition states that the answer is yes.

Encoding.  Graphs are finite and simple.  The constants are c = 1/q and ε = 1/p, without loss of
generality as W >= 1.  Then |X| >= ε W becomes W <= p |X|, and |Y| >= ε W^c becomes
W <= (p |Y|)^q. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between (G : sgraph) (A B : {set G}) : bool :=
  [forall a in A, [forall b in B, a -- b]].

(** [T] is a triangle: a clique on three vertices. *)
Definition triangle (G : sgraph) (T : {set G}) : Prop := clique T /\ #|T| = 3.

(** ** Definitions specific to the conjecture *)

(** [B] is a blockade of length 3: the sets [B i] are nonempty and pairwise disjoint. *)
Definition blockade3 (G : sgraph) (B : 'I_3 -> {set G}) : Prop :=
  (forall i : 'I_3, B i != set0) /\ (forall i j : 'I_3, i != j -> [disjoint B i & B j]).

(** The width of [B]: the minimum size of the sets [B i]. *)
Definition blockade3_width (G : sgraph) (B : 'I_3 -> {set G}) : nat :=
  \big[minn/#|B ord0|]_(i < 3) #|B i|.

(** There is a triangle with exactly one vertex in each [B i]. *)
Definition transversal_triangle (G : sgraph) (B : 'I_3 -> {set G}) : Prop :=
  exists T : {set G}, triangle T /\ forall i : 'I_3, #|T :&: B i| = 1.

(** ** Statement *)

Definition AX_pure_pairs_blockade_transversal_triangle_polynomial : Prop :=
  exists p q : nat, [/\ 0 < p, 0 < q &
    forall (G : sgraph) (B : 'I_3 -> {set G}),
      blockade3 B -> ~ transversal_triangle B ->
      exists (i j : 'I_3) (X Y : {set G}),
        [/\ i != j, X \subset B i, Y \subset B j,
            complete_between X Y || anticomplete X Y &
            blockade3_width B <= p * #|X| /\ blockade3_width B <= (p * #|Y|) ^ q]].
