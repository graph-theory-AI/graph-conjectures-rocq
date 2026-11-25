(** * Ryser's conjecture

Ryser; Open Problem Garden, rysers_conjecture.

A hypergraph is r-partite and r-uniform if its vertices can be partitioned into r parts such that
every edge has exactly one vertex in each part.  The matching number ν is the maximum number of
pairwise disjoint edges, and the cover number τ is the minimum size of a set of vertices that meets
all edges.

Conjecture: τ <= (r - 1) ν for every r-partite r-uniform hypergraph.

Encoding.  r >= 2 is assumed, as in the literature (for r = 1 we have τ = ν, hence the inequality
fails if there is an edge).  ν and τ are given by their characterizations. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E M : {set {set T}}) (e X : {set T}).

(** [E] is [k]-partite and [k]-uniform for the partition given by [part]: every edge has exactly
    one vertex in each part. *)
Definition hg_partite_uniform (k : nat) (part : T -> 'I_k) E : Prop :=
  forall e, e \in E -> forall j : 'I_k, #|[set v in e | part v == j]| = 1.

(** [M] is a matching: a set of pairwise disjoint edges. *)
Definition hg_matching M E : Prop :=
  M \subset E /\ trivIset M.

(** The matching number (maximum number of edges of a matching) of [E] is [nu]. *)
Definition hg_matching_number E (nu : nat) : Prop :=
  (exists M : {set {set T}}, hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, hg_matching M E -> #|M| <= nu).

(** [X] is a vertex cover (transversal): it meets all edges. *)
Definition hg_cover X E : Prop :=
  forall e : {set T}, e \in E -> X :&: e != set0.

(** The vertex cover number (minimum size of a vertex cover) of [E] is [tau]. *)
Definition hg_cover_number E (tau : nat) : Prop :=
  (exists X : {set T}, hg_cover X E /\ #|X| = tau) /\
  (forall X : {set T}, hg_cover X E -> tau <= #|X|).

End Hypergraph.

(** ** Statement *)

Definition OPG_ryser_r_partite_hypergraph_cover_matching : Prop :=
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (nu tau : nat),
    1 < r ->
    hg_partite_uniform part E ->
    hg_matching_number E nu ->
    hg_cover_number E tau ->
    tau <= (r - 1) * nu.
