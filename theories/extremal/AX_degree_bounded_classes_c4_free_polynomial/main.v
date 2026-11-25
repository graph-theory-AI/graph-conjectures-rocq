(** * C_4-free subgraphs of large average degree

Du, Girão, Hunter, McCarty, Scott, "Induced C_4-free subgraphs with large average degree",
arXiv:2307.08361 (2307.08361__01).

A graph is C_4-free if it has no subgraph isomorphic to C_4.  Subgraphs are not necessarily induced.

Question: is there a polynomial p such that every graph of average degree at least p(k) contains a
C_4-free subgraph of average degree at least k?

The proposition states that the answer is yes.

Encoding.  Graphs are finite, simple and nonempty.  The polynomial has coefficients in nat, which is
not a restriction, as p can be increased.  It is the list [p] of its coefficients, and
[horner_rec p k] is its value at k. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot algebra.

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

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Statement *)

Definition AX_degree_bounded_classes_c4_free_polynomial : Prop :=
  exists p : seq nat, forall (k : nat) (G : sgraph),
    0 < #|G| -> average_degree_ge G (horner_rec p k) 1 ->
    exists H : sgraph,
      [/\ 0 < #|H|, subgraph H G, ~ subgraph (cycle_graph 4) H & average_degree_ge H k 1].
