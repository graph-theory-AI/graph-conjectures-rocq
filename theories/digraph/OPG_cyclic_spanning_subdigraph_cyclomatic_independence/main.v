(** * Cyclic spanning subdigraphs with small cyclomatic number

Bondy, "Basic graph theory: paths and circuits", Handbook of Combinatorics, Vol. 1, 1995;
Open Problem Garden, cyclic_spanning_subdigraph_with_small_cyclomatic_number.

A strong component of a digraph is trivial if it has a single vertex.  A digraph is cyclic if it
is a disjoint union of nontrivial strong digraphs, or equivalently if it has no isolated vertex
and each of its arcs lies on a directed cycle.  The cyclomatic number of a digraph with n
vertices, m arcs and c connected components (of the underlying graph) is m - n + c.  It is
m - n + 1 for a strong digraph.  The independence number α(D) is the maximum number of pairwise
nonadjacent vertices of D.

Conjecture: every digraph D whose strong components are all nontrivial contains a cyclic
spanning subdigraph with cyclomatic number at most α(D).

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--], assumed irreflexive (no loop).  Digons are allowed, and they are directed
cycles.  Parallel arcs are not represented (they are useless here).  As there is no loop, the
strong components are nontrivial if and only if every vertex lies on a directed cycle.  A
spanning subdigraph is given by its arc set.  It may have several connected components, hence
the general form m - n + c of the cyclomatic number (for instance, a disjoint union of p
directed cycles has cyclomatic number p), although the Open Problem Garden gives m - n + 1. *)

From GraphTheory Require Import preliminaries sgraph digraph.
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

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The arcs of the directed cycle [c]. *)
Definition dicycle_arcs (D : diGraph) (c : seq D) : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** Independence number. *)
Definition digraph_alpha (D : diGraph) : nat := \max_(S : {set D} | arc_free S) #|S|.

(** ** Definitions specific to the conjecture *)

(** [F] is the arc set of a cyclic spanning subdigraph of [D]: [F] consists of arcs of [D], each
    vertex is the tail of an arc of [F], and each arc of [F] lies on a directed cycle of arcs
    of [F]. *)
Definition cyclic_spanning (D : diGraph) (F : {set D * D}) : Prop :=
  let B := digraph_of_arcs F in
  [/\ F \subset arcs D,
      forall v : B, exists w : B, v -- w
    & forall v w : B, v -- w -> exists2 c : seq B, dicycle c & (v, w) \in dicycle_arcs c].

(** The cyclomatic number of the spanning subdigraph with arc set [F] (the subtraction is not
    truncated, as m + c >= n). *)
Definition arcs_cyclomatic_number (D : diGraph) (F : {set D * D}) : nat :=
  #|F| + #|components [set: underlying (digraph_of_arcs F)]| - #|D|.

(** ** Statement *)

Definition OPG_cyclic_spanning_subdigraph_cyclomatic_independence : Prop :=
  forall D : diGraph, irreflexive (@edge_rel D) ->
    (forall v : D, exists2 c : seq D, dicycle c & v \in c) ->
    exists2 F : {set D * D}, cyclic_spanning F & arcs_cyclomatic_number F <= digraph_alpha D.
