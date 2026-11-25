(** * Book thickness of subdivisions

Blankenship, Oporowski, "Drawing Subdivisions Of Complete And Complete Bipartite Graphs On
Books", Technical Report 1999-4, Louisiana State University; Open Problem Garden,
book_thickness_of_subdivisions.

A k-page book embedding of a graph G is a linear order of its vertices and a colouring of its
edges with k colours such that edges with the same colour do not cross: there are no edges vw
and xy with the same colour such that v < x < w < y.  The book thickness bt(G) is the minimum
integer k for which there is a k-page book embedding of G.  Let G' be the graph obtained by
subdividing each edge of G exactly once.

Conjecture: there is a function f such that bt(G) <= f(bt(G')) for every graph G.

Encoding.  Graphs are finite and simple.  The colouring is defined on all pairs of vertices, so
that the book thickness of a nonempty graph without edges is 1 instead of 0, which does not
change the conjecture.  The book thickness is a relation between G and k. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

Section Subdivision.
Variables (G : sgraph) (n : nat).

(** The edges, with a fixed orientation. *)
Definition oriented_edge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

Local Abbreviation EdgeT := {p : G * G | oriented_edge p}.

(** The vertices of the subdivision: those of [G], and [n-1] vertices for each edge. *)
Definition subdivision_vertex : Type := (G + (EdgeT * 'I_n.-1))%type.

(** The edges of the subdivision, in one direction. *)
Definition subdivision_rel (x y : subdivision_vertex) : bool :=
  match x, y with
  | inl _, inl _ => false
  | inl a, inr (e, i) =>
      ((a == (val e).1) && (val i == 0)) || ((a == (val e).2) && (val i == n.-1.-1))
  | inr _, inl _ => false
  | inr (e, i), inr (e', j) => (e == e') && ((val i).+1 == val j)
  end.

(** [G] with each edge replaced by a path of length [n] ([2 <= n] is meant). *)
Definition subdivision : sgraph := sgraph_of_rel subdivision_rel.

End Subdivision.

(** [G] has a book embedding with [k] pages: an order of its vertices and an assignment of its
    edges to [k] pages without crossing edges on a page. *)
Definition book_embedding (G : sgraph) (k : nat) : Prop :=
  exists (pos : G -> nat) (col : G -> G -> nat),
    [/\ injective pos,
        (forall x y : G, col x y = col y x),
        (forall x y : G, col x y < k) &
        (forall a b c d : G,
           a -- b -> c -- d -> col a b = col c d ->
           ~~ ((pos a < pos c) && (pos c < pos b) && (pos b < pos d)))].

(** The book thickness (page number) of [G] is [k]. *)
Definition book_thickness (G : sgraph) (k : nat) : Prop :=
  book_embedding G k /\ (forall m : nat, book_embedding G m -> k <= m).

(** ** Statement *)

Definition OPG_book_thickness_subdivision_bounded_function : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (bG bG' : nat),
      book_thickness G bG ->
      book_thickness (subdivision G 2) bG' ->
      bG <= f bG'.
