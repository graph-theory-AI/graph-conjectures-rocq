(** * 3-colourability of ternary graphs

Chudnovsky, Scott, Seymour, Spirkl, "Proof of the Kalai-Meshulam conjecture", arXiv:1810.00065, open
problem of the introduction (1810.00065__00).

A graph is ternary if none of its induced cycles has length a multiple of three.

The authors say that it may be that all ternary graphs are 3-colourable, and this is what is
stated.

Encoding.  Graphs are finite and simple.  Induced cycles have length at least 3, so ternary graphs
are triangle-free. *)

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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions specific to the conjecture *)

(** [G] is ternary: it has no induced cycle of length [k] for any multiple [k] of 3. *)
Definition ternary (G : sgraph) : Prop :=
  forall k : nat, 3 <= k -> 3 %| k -> ~ has_induced_copy G (cycle_graph k).

(** ** Statement *)

Definition AX_ternary_graphs_3_colorable : Prop :=
  forall G : sgraph, ternary G -> χ([set: G]) <= 3.
