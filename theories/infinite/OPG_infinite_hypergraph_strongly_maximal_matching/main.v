(** * Strongly maximal matchings and strongly minimal covers

Aharoni, "Infinite matching theory", Discrete Math. 95 (1991), 5-22; Open Problem Garden,
strong_matchings_and_covers.

In a hypergraph H, a strongly maximal matching is a matching F such that |F' \ F| <= |F \ F'| for
every matching F'.  A strongly minimal cover is a vertex cover X such that |X' \ X| >= |X \ X'| for
every vertex cover X'.

Conjecture: every (possibly infinite) hypergraph in which all edges have size at most k, for some
integer k, has a strongly maximal matching and a strongly minimal cover.

Encoding.  Hypergraphs have arbitrary types of vertices and edges, and an incidence relation in
[Prop].  Parallel edges are allowed, which is not more general as a matching contains at most one
edge of each parallel class.  The edges are nonempty, as a hypergraph with an empty edge has no
cover; this guard is implicit in the source.  Cardinalities are compared by injections. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/infinite.v *)

(** [P] is at most as large as [Q]. *)
Definition icard_le (A B : Type) (P : A -> Prop) (Q : B -> Prop) : Prop :=
  exists f : {x : A | P x} -> {y : B | Q y}, injective f.

(** Hypergraphs, possibly infinite, with an incidence relation. *)
Record iHypergraph := Build_iHypergraph {
  ihg_vertex : Type;
  ihg_edge : Type;
  ihg_incident : ihg_edge -> ihg_vertex -> Prop }.

(** [F] is a matching: distinct edges of [F] have no common vertex. *)
Definition ihg_matching (H : iHypergraph) (F : ihg_edge H -> Prop) : Prop :=
  forall e1 e2, F e1 -> F e2 -> (exists v, ihg_incident e1 v /\ ihg_incident e2 v) -> e1 = e2.

(** [X] is a vertex cover: it meets all edges. *)
Definition ihg_cover (H : iHypergraph) (X : ihg_vertex H -> Prop) : Prop :=
  forall e : ihg_edge H, exists v, X v /\ ihg_incident e v.

(** The matching [F] is strongly maximal: for each matching [F'], the set [F' \ F] is at most as
    large as [F \ F']. *)
Definition strongly_maximal_matching (H : iHypergraph) (F : ihg_edge H -> Prop) : Prop :=
  ihg_matching F /\
  forall F' : ihg_edge H -> Prop, ihg_matching F' ->
    icard_le (fun e => F' e /\ ~ F e) (fun e => F e /\ ~ F' e).

(** The cover [X] is strongly minimal: for each cover [X'], the set [X \ X'] is at most as large
    as [X' \ X]. *)
Definition strongly_minimal_cover (H : iHypergraph) (X : ihg_vertex H -> Prop) : Prop :=
  ihg_cover X /\
  forall X' : ihg_vertex H -> Prop, ihg_cover X' ->
    icard_le (fun v => X v /\ ~ X' v) (fun v => X' v /\ ~ X v).

(** ** Definitions specific to the conjecture *)

(** The edge [e] has at most [k] vertices. *)
Definition ihg_edge_size_le (H : iHypergraph) (k : nat) (e : ihg_edge H) : Prop :=
  exists g : 'I_k -> ihg_vertex H, forall v, ihg_incident e v -> exists i, g i = v.

(** ** Statement *)

Definition OPG_infinite_hypergraph_strongly_maximal_matching : Prop :=
  forall (H : iHypergraph) (k : nat),
    (forall e : ihg_edge H, exists v, ihg_incident e v) ->
    (forall e : ihg_edge H, ihg_edge_size_le k e) ->
    (exists F : ihg_edge H -> Prop, strongly_maximal_matching F) /\
    (exists X : ihg_vertex H -> Prop, strongly_minimal_cover X).
