(** * The Erdős–Pósa property for planar minors, with bound O(k log k)

Aboulker, Fiorini, Huynh, Joret, Raymond, Sau, "A tight Erdős-Pósa function for wheel minors",
SIAM J. Discrete Math. 32 (2018), arXiv:1710.06282, Conjecture 1.2 (1710.06282__00).

An H-model in G is a family of disjoint connected subgraphs S_x of G, for x in V(H), such that S_x
and S_y are joined by an edge of G whenever x y is an edge of H.  Let ν_H(G) be the maximum number
of vertex-disjoint H-models in G, and τ_H(G) the minimum size of a set X of vertices such that
G - X has no H-model.  The Erdős–Pósa property holds for H-models with bounding function f if
τ_H(G) <= f(ν_H(G)) for every graph G.

Conjecture 1.2: for every planar graph H, the Erdős–Pósa property holds for H-models with a
bounding function in O(k log k).

Encoding.  Graphs are finite and simple.  A graph is planar if it has no minor K_5 or K_{3,3}.
The property says that for k >= 1, G has k disjoint H-models or a set of at most
C k (1 + ⌊log_2(k+1)⌋) vertices that meets all the H-models, where C depends only on H. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** The vertices of an [H]-model, given by its branch sets. *)
Definition model_vertices (G H : sgraph) (branch : H -> {set G}) : {set G} :=
  \bigcup_(h : H) branch h.

(** [G] has [k] vertex-disjoint [H]-models. *)
Definition disjoint_models (G H : sgraph) (k : nat) : Prop :=
  exists branch : 'I_k -> H -> {set G},
    (forall i : 'I_k, minor_rmap (branch i)) /\
    forall i j : 'I_k, i != j ->
      model_vertices (branch i) :&: model_vertices (branch j) = set0.

(** [X] meets all the [H]-models of [G]. *)
Definition model_hitting_set (G H : sgraph) (X : {set G}) : Prop :=
  forall branch : H -> {set G},
    minor_rmap branch -> model_vertices branch :&: X != set0.

(** The Erdős–Pósa property holds for [H]-models with a bounding function in O(k log k). *)
Definition erdos_posa_k_log_k (H : sgraph) : Prop :=
  exists C : nat,
    forall (G : sgraph) (k : nat),
      1 <= k ->
      disjoint_models G H k \/
      exists X : {set G},
        #|X| <= C * k * (trunc_log 2 k.+1).+1 /\ model_hitting_set H X.

(** ** Statement *)

Definition AX_erdos_posa_planar_minor_k_log_k : Prop :=
  forall H : sgraph, planar H -> erdos_posa_k_log_k H.
