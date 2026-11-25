(** * Separation choosability and minimum degree

Esperet, Kang, Thomassé, "Separation choosability and dense bipartite induced subgraphs", Combin.
Probab. Comput. 28 (2019), arXiv:1802.03727, Conjecture 1.3 (1802.03727__00).

A k-list-assignment of a graph G gives to each vertex v a list L(v) of k colours; it has maximum
separation if |L(u) ∩ L(v)| <= 1 for every edge uv.  G is separation k-choosable if for every
k-list-assignment L with maximum separation, it has a proper colouring from the lists L.  The
separation choosability ch_sep(G) is the least such k.

Conjecture 1.3: there is a function x such that x(d) tends to infinity with d, and
ch_sep(G) >= x(d) for any graph G with minimum degree d.

Encoding.  Graphs are finite, simple and nonempty.  The function x is only required to be
unbounded, and G has minimum degree at least d.  This is equivalent: the maximum of x(d') over
d' <= d is then a nondecreasing unbounded function; conversely, take the minimum of x(d') over
d' >= d.  "ch_sep(G) >= k" means that G is not separation j-choosable for any j < k. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** The lists have size [k], and those of adjacent vertices have at most one common colour. *)
Definition separated_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (k : nat) : Prop :=
  (forall v : G, #|L v| = k) /\
  forall u v : G, u -- v -> #|L u :&: L v| <= 1.

(** [G] can be coloured from all separated lists of size [k]. *)
Definition separation_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    separated_lists L k -> list_colorable L.

(** ** Definitions specific to the conjecture *)

(** The separation choosability of [G] is at least [k]. *)
Definition separation_choosability_geq (G : sgraph) (k : nat) : Prop :=
  forall j : nat, j < k -> ~ separation_choosable G j.

(** ** Statement *)

Definition AX_separation_choosability_grows_min_degree : Prop :=
  exists x : nat -> nat,
    (forall B : nat, exists d : nat, B <= x d) /\
    forall (d : nat) (G : sgraph),
      0 < #|G| -> min_degree_ge G d -> separation_choosability_geq G (x d).
