(** * Books versus triangles at the extremal density

Conlon, Fox, Sudakov, "Books versus triangles at the extremal density", arXiv:1905.05312,
Conjecture 1.1 (1905.05312__00).

The book number of a graph is the maximum number of triangles that contain a given edge.  For
b <= n/4, the graph S_(b,n) is the blow-up of the 3-prism with parts U_1, U_2, U_3, V_1, V_2, V_3,
where |U_1| = |U_2| = |V_1| = |V_2| = b, |U_3| = ⌊(n-4b)/2⌋ and |V_3| = ⌈(n-4b)/2⌉: U_i is
complete to U_j and V_i to V_j for i <> j, U_i is complete to V_i for each i, and there are no
other edges.

Conjecture 1.1: if n/6 <= b < n/4, then every graph on n vertices with at least ⌊n^2/4⌋ edges and
book number at most b which is not the balanced complete bipartite graph has at least b^2(n-4b)
triangles, with equality if and only if the graph is S_(b,n).

Encoding.  "Is" means "is isomorphic to".  An isomorphism to S_(b,n) is given by the parts of the
vertices: U_1, U_2, U_3, V_1, V_2, V_3 have indices 0, 1, 2, 3, 4, 5. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** The number of cliques of [G] on [r] vertices. *)
Definition clique_count_size (G : sgraph) (r : nat) : nat :=
  #|[set S in cliques [set: G] | #|S| == r]|.

(** ** Definitions specific to the conjecture *)

(** The book number of [G] is at most [b]: the ends of each edge have at most [b] common
    neighbours. *)
Definition book_number_le (G : sgraph) (b : nat) : Prop :=
  forall x y : G, x -- y -> #|common_neigh x y| <= b.

(** The 3-prism on 0, ..., 5: the triangles 0 1 2 and 3 4 5, and the edges 0 3, 1 4 and 2 5. *)
Definition prism_rel (i j : nat) : bool :=
  (i != j) && (((i < 3) == (j < 3)) || (i %% 3 == j %% 3)).

(** [G] is isomorphic to S_([b],[n]) ([4 * b <= n] is meant): [p] gives the part of each vertex. *)
Definition is_S (b n : nat) (G : sgraph) : Prop :=
  exists p : G -> 'I_6,
    (forall x y : G, (x -- y) = prism_rel (p x) (p y)) /\
    (forall i : 'I_6, #|[set x | p x == i]| =
       nth 0 [:: b; b; (n - 4 * b) %/ 2; b; b; (n - 4 * b) - (n - 4 * b) %/ 2] i).

(** ** Statement *)

Definition AX_book_number_triangle_count_extremal_density : Prop :=
  forall (n b : nat) (G : sgraph),
    n <= 6 * b -> 4 * b < n -> #|G| = n ->
    n ^ 2 %/ 4 <= #|E(G)| -> book_number_le G b ->
    ~ inhabited (diso G 'K_(n %/ 2),(n - n %/ 2)) ->
    b ^ 2 * (n - 4 * b) <= clique_count_size G 3 /\
    (clique_count_size G 3 = b ^ 2 * (n - 4 * b) <-> is_S b n G).
