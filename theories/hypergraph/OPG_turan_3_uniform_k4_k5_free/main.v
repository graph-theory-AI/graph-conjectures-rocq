(** * Turán's problem for 3-uniform hypergraphs without K_4 or K_5

Turán, "Eine Extremalaufgabe aus der Graphentheorie", Mat. Fiz. Lapok 48 (1941); Open Problem
Garden, turans_problem_for_hypergraphs.

The complete 3-uniform hypergraph on m vertices has all sets of 3 vertices as edges.

Conjecture, in two parts:
- every simple 3-uniform hypergraph on 3n vertices that contains no complete 3-uniform hypergraph
  on 4 vertices has at most n^2 (5n - 3) / 2 edges;
- every simple 3-uniform hypergraph on 2n vertices that contains no complete 3-uniform hypergraph
  on 5 vertices has at most n^2 (n - 1) edges.

Encoding.  The proposition is the conjunction of both parts, for n >= 1 (for n = 0 there are no
vertices and no edges).  Edges are sets, hence not repeated. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** [E] contains a copy of [F]. *)
Definition hg_contains (S T : finType) (F : {set {set S}}) (E : {set {set T}}) : bool :=
  [exists f : {ffun S -> T},
     injectiveb f && [forall e in F, [set f x | x in e] \in E]].

(** ** Definitions specific to the conjecture *)

(** The complete 3-uniform hypergraph on [m] vertices. *)
Definition complete_3_uniform (m : nat) : {set {set 'I_m}} := [set e : {set 'I_m} | #|e| == 3].

(** ** Statement *)

Definition OPG_turan_3_uniform_k4_k5_free : Prop :=
  forall (n : nat) (T : finType) (E : {set {set T}}),
    0 < n ->
    hg_uniform E 3 ->
    (#|T| = 3 * n -> ~ hg_contains (complete_3_uniform 4) E -> 2 * #|E| <= n ^ 2 * (5 * n - 3)) /\
    (#|T| = 2 * n -> ~ hg_contains (complete_3_uniform 5) E -> #|E| <= n ^ 2 * (n - 1)).
