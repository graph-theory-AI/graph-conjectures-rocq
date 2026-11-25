(** * Partial list colouring

Albertson, Grossman, Haas, "Partial list colouring", Discrete Math. 214 (2000); Open Problem Garden,
partial_list_coloring.

The list chromatic number χ_l(G) is the minimum k such that G has a proper colouring from all lists
of at least k colours on its vertices.

Conjecture: let G be a graph with n vertices, let 0 <= t <= χ_l(G), and assign a list of t colours
to each vertex of G.  Then at least t n / χ_l(G) vertices of G can be coloured from these lists
(they induce a subgraph that has a proper colouring from its lists).

Encoding.  Graphs are finite and simple.  The inequality is multiplied by χ_l(G).
"χ_l(G) = c" is a relation between G and c. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition OPG_partial_list_coloring_tn_over_chi : Prop :=
  forall (G : sgraph) (t cl : nat),
    choice_number G cl -> t <= cl ->
    forall (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) ->
      exists W : {set G},
        list_colorable (fun v : induced W => L (val v)) /\ t * #|G| <= cl * #|W|.
