(** * List chromatic number and maximum degree of bipartite graphs

Alon; Open Problem Garden, list_chromatic_number_and_maximum_degree_of_bipartite_graphs.

Conjecture: there is a constant c such that the list chromatic number of any bipartite graph G of
maximum degree Δ is at most c log Δ.

Encoding.  Graphs are finite and simple.  "The list chromatic number of G is m" is a relation
between G and m (it exists for all G).  The logarithm is in base 2, which only changes c, and
m <= c log Δ is expressed as 2^m <= Δ^c.  The constant c is a natural number, which is not a
restriction as log Δ >= 0.  The statement is restricted to Δ >= 2: it is false in the degenerate
case Δ = 1, as a single edge has list chromatic number 2. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

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

Definition OPG_bipartite_list_chromatic_log_max_degree : Prop :=
  exists c : nat,
    forall (G : sgraph) (m : nat),
      bipartite G -> 2 <= Delta G -> choice_number G m -> 2 ^ m <= Delta G ^ c.
