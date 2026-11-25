(** * Dichromatic number of digraphs without induced odd directed cycle

Carbonero, Hompe, Moore, Spirkl, "A counterexample to a conjecture about triangle-free induced
subgraphs of graphs with large chromatic number", 2022, arXiv:2201.08204, Question 3.2
(2201.08204__01).

Digraphs have no loop and at most one arc between two distinct vertices.  The clique number ω(D) of
a digraph D is the one of its underlying graph.  The dichromatic number of D is the least k such
that its vertices can be partitioned into k sets that induce acyclic subdigraphs.

Question: is there a function f such that the dichromatic number of every digraph D with no induced
directed cycle of odd length is at most f(ω(D))?

Encoding.  The positive answer is stated.  Digraphs are those of GraphTheory ([diGraph]: a finite
type of vertices with a boolean relation [--]), with the hypothesis that they are oriented (no loop,
no digon), as in the source.  A directed cycle is induced if the only arcs between its vertices are
its own arcs.  Directed triangles are excluded too. *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
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

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The directed cycle [c] is induced: the arcs between its vertices are those of [c]. *)
Definition induced_dicycle (D : diGraph) (c : seq D) : Prop :=
  dicycle c /\ {in c &, forall u v : D, u -- v -> next c u = v}.

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** ** Statement *)

Definition AX_odd_dicycle_free_digraph_dichromatic_bounded : Prop :=
  exists f : nat -> nat,
    forall D : diGraph, oriented D ->
      (forall c : seq D, induced_dicycle c -> ~~ odd (size c)) ->
      dicolorable D (f (ω([set: underlying D]))).
