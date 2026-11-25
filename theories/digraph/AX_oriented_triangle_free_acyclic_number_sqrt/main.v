(** * Minimum acyclic number of oriented triangle-free graphs

Aboulker, Havet, Pirot, Schabanel, "Minimum acyclic number and maximum dichromatic number of
oriented triangle-free graphs of a given order", arXiv:2403.02298, Conjecture 3 (2403.02298__00).

An oriented graph is a digraph without loop and without digon.  It is triangle-free if its
underlying graph has no triangle.  The acyclic number of a digraph is the maximum number of vertices
of an acyclic induced subdigraph.  Let a(n) be the minimum acyclic number of an oriented
triangle-free graph on n vertices.

Conjecture 3: a(n) = Θ(√(n log n)).

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  The function a is given by the relation "a is the minimum acyclic number for n"; it
exists, as the edgeless graphs are oriented triangle-free graphs.  The square root is rounded up and
the logarithm is the integer part of the binary logarithm, which only changes the constants. *)

From GraphTheory Require Import preliminaries sgraph digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sqrt_ceil_ex (n : nat) : exists s : nat, n <= s ^ 2.
Proof. by exists n; rewrite expnS expn1; case: n => // m; rewrite leq_pmulr. Qed.

(** The ceiling of the square root of [n]: the least [s] such that [n <= s ^ 2]. *)
Definition sqrt_ceil (n : nat) : nat := ex_minn (sqrt_ceil_ex n).

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f = O(g)]. *)
Definition big_O_nat (f g : nat -> nat) : Prop :=
  exists C : nat, 0 < C /\ eventually (fun n => f n <= C * g n).

(** [f = Theta(g)]. *)
Definition big_Theta_nat (f g : nat -> nat) : Prop :=
  big_O_nat f g /\ big_O_nat g f.

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The maximum size of a set inducing an acyclic digraph. *)
Definition acyclic_number (D : diGraph) : nat :=
  \max_(S : {set D} | acyclic (induced S)) #|S|.

(** ** Definitions specific to the conjecture *)

(** [a] is the minimum acyclic number of an oriented triangle-free graph on [n] vertices. *)
Definition min_acyclic_number (n a : nat) : Prop :=
  (forall D : diGraph, oriented D -> triangle_free (underlying D) -> #|D| = n ->
     a <= acyclic_number D) /\
  exists D : diGraph,
    [/\ oriented D, triangle_free (underlying D), #|D| = n & acyclic_number D = a].

(** ** Statement *)

Definition AX_oriented_triangle_free_acyclic_number_sqrt : Prop :=
  forall a : nat -> nat, (forall n : nat, min_acyclic_number n (a n)) ->
    big_Theta_nat a (fun n => sqrt_ceil (n * trunc_log 2 n)).
