(** * Chromatic number of the 3/3-power of a graph

Mozafari-Nia, Iradmusa; Open Problem Garden, chromatic_number_of_frac_3_3_power_of_graph.

The m-th power G^m of a graph G has the same vertices as G, and any two distinct vertices at
distance at most m in G are adjacent in G^m.  The n-subdivision G^(1/n) is obtained by replacing
each edge of G by a path of length n.  The fractional power G^(m/n) is (G^(1/n))^m.

Conjecture: if G is a graph with Δ(G) >= 2, then χ(G^(3/3)) <= 2Δ(G) + 1.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** The [m]-th power of [G]: distinct vertices at distance at most [m] are adjacent. *)
Definition graph_power (G : sgraph) (m : nat) : sgraph :=
  sgraph_of_rel (fun x y : G => y \in ball m x).

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

(** The fractional power [G^(m/n)]: the [m]-th power of the [n]-subdivision of [G]
    ([2 <= n] is meant). *)
Definition fractional_power (G : sgraph) (m n : nat) : sgraph := graph_power (subdivision G n) m.

(** ** Statement *)

Definition OPG_fractional_power_chromatic_3_3_2_delta : Prop :=
  forall G : sgraph, 2 <= Delta G -> χ([set: fractional_power G 3 3]) <= 2 * Delta G + 1.
