(** * Choice number of k-chromatic graphs of bounded order

Noel, "Choosability of graphs with bounded order: Ohba's conjecture and beyond", Master's thesis,
McGill University, 2013; Open Problem Garden,
choice_number_of_k_chromatic_graphs_of_bounded_order.

A graph G is k-choosable if it has a proper colouring from all lists of at least k colours on its
vertices.  The choice number ch(G) is the minimum k such that G is k-choosable.  K_{m*k} is the
complete k-partite graph in which every part has m vertices.

Conjecture: if G is a k-chromatic graph on at most mk vertices, then ch(G) <= ch(K_{m*k}).

Encoding.  Graphs are finite and simple.  "ch(G) = c" is a relation between G and c. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section CompleteMultipartite.
Variables k m : nat.

(** Vertices in different parts. *)
Definition complete_multipartite_rel : rel ('I_k * 'I_m) := fun x y => x.1 != y.1.

Lemma complete_multipartite_sym : symmetric complete_multipartite_rel.
Proof. by move=> x y; rewrite /complete_multipartite_rel eq_sym. Qed.

Lemma complete_multipartite_irrefl : irreflexive complete_multipartite_rel.
Proof. by move=> x; rewrite /complete_multipartite_rel eqxx. Qed.

(** The complete multipartite graph with [k] parts of size [m]. *)
Definition complete_multipartite : sgraph :=
  SGraph complete_multipartite_sym complete_multipartite_irrefl.

End CompleteMultipartite.

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

Definition OPG_choice_number_k_chromatic_mk_vertices : Prop :=
  forall (G : sgraph) (k m chG chK : nat),
    χ([set: G]) = k -> #|G| <= m * k ->
    choice_number G chG ->
    choice_number (complete_multipartite k m) chK ->
    chG <= chK.
