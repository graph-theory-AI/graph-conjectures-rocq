(** * List colourings of complete multipartite graphs with two big parts

Allagan, "Choice numbers, Ohba numbers and Hall numbers of some complete k-partite graphs", PhD
thesis, Auburn University, 2009; Open Problem Garden,
list_colourings_of_complete_multipartite_graphs_with_2_big_parts.

The choice number (list chromatic number) ch(G) of a graph G is the minimum k such that G has a
proper colouring from all lists of k colours on its vertices.  G is chromatic-choosable if
ch(G) = χ(G).  The join G + H of two graphs is obtained from disjoint copies of G and H by adding
all edges between them.

Question: given a, b >= 2, what is the smallest integer t >= 0 such that K_{a,b} + K_t is
chromatic-choosable?

Let φ(a,b) be this integer (Ohba proved that it exists).  The proposition only states the bounds on
φ(a,b) that the Open Problem Garden gives with the question: for all a, b >= 2, φ(a,b) exists and

- φ(a,b) >= ch(K_{a,b}) - 2, and φ(a,b) <= a + b - 5 if a + b >= 5 (Noel, Reed, Wu);
- ⌊√a⌋ - 1 <= φ(a,2) <= ⌈(√(8a + 17) - 7) / 2⌉ if a >= 5 (Allagan).

Encoding.  The question suggests no formula for φ(a,b): the proposition is a proxy, weaker than a
determination of φ(a,b).  Graphs are finite and simple.  "ch(G) = c" is a relation between G and c.
The inequality ch(K_{a,b}) <= t + 2 is expressed as: K_{a,b} is (t+2)-choosable.  The subtraction
a + b - 5 is truncated, which adds that φ(2,2) = 0.  For natural numbers, ⌊√a⌋ - 1 <= t means
a < (t+2)², and t <= ⌈(√(8a + 17) - 7) / 2⌉ means (2t+5)² < 8a + 17. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section GraphJoin.
Variables G H : sgraph.

(** The edges of [G], those of [H], and all pairs of a vertex of [G] and a vertex of [H]. *)
Definition graph_join_rel : rel (G + H)%type := fun u v =>
  match u, v with
  | inl x, inl y => x -- y
  | inr x, inr y => x -- y
  | _, _ => true
  end.

Lemma graph_join_sym : symmetric graph_join_rel.
Proof. by move=> [x|x] [y|y] //=; rewrite sgP. Qed.

Lemma graph_join_irrefl : irreflexive graph_join_rel.
Proof. by move=> [x|x] /=; rewrite sgP. Qed.

(** The join of [G] and [H]. *)
Definition graph_join : sgraph := SGraph graph_join_sym graph_join_irrefl.

End GraphJoin.

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

(** The choice number of [G] is its chromatic number. *)
Definition chromatic_choosable (G : sgraph) : Prop := choice_number G (χ([set: G])).

(** ** Definitions specific to the conjecture *)

(** [t] is the smallest integer such that [G + K_t] is chromatic-choosable. *)
Definition least_choosable_join (G : sgraph) (t : nat) : Prop :=
  chromatic_choosable (graph_join G 'K_t) /\
  (forall t', chromatic_choosable (graph_join G 'K_t') -> t <= t').

(** ** Statement *)

Definition proxy_OPG_complete_multipartite_two_big_parts_choosability : Prop :=
  forall a b : nat, 2 <= a -> 2 <= b ->
    exists t : nat,
      [/\ least_choosable_join 'K_a,b t,
          choosable 'K_a,b (t + 2),
          t <= a + b - 5 &
          b = 2 -> 5 <= a -> a < (t + 2) ^ 2 /\ (2 * t + 5) ^ 2 < 8 * a + 17].
