(** * Choice number of squares of graphs

Noel (2013); Open Problem Garden, choosability_of_graph_powers.

The square G² of a graph G is obtained by joining any two distinct vertices at distance at most 2.
The choice number ch(H) of H is the minimum k such that H has a proper colouring from all lists of
k colours on its vertices.

Question: does there exist a function f(k) = o(k²) such that ch(G²) <= f(χ(G²)) for every graph G?
The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  "ch(H) = m" is a relation between H and m (it exists for
all H).  The values of f are natural numbers, which is not a restriction (round them down), and
f(k) = o(k²) means: for all c > 0, c f(k) <= k² for every sufficiently large k. *)

From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** The [m]-th power of [G]: distinct vertices at distance at most [m] are adjacent. *)
Definition graph_power (G : sgraph) (m : nat) : sgraph :=
  sgraph_of_rel (fun x y : G => y \in ball m x).

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

(** ** Definitions specific to the conjecture *)

(** [f(k) = o(k^2)]. *)
Definition little_o_square (f : nat -> nat) : Prop :=
  forall c : nat, 0 < c -> eventually (fun k => c * f k <= k * k).

(** ** Statement *)

Definition OPG_graph_square_choice_number_subquadratic : Prop :=
  exists f : nat -> nat, little_o_square f /\
    forall (G : sgraph) (m : nat),
      choice_number (graph_power G 2) m -> m <= f (χ([set: graph_power G 2])).
