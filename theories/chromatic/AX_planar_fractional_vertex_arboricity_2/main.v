(** * Fractional vertex-arboricity of planar graphs

Bonamy, Kardoš, Kelly, Postle, "Fractional vertex-arboricity of planar graphs", arXiv:2009.12189,
Conjecture 1.1 (2009.12189__00).

The fractional vertex-arboricity va_f(G) is the minimum of Σ_F x_F over the weightings x >= 0 of the
sets F of vertices that induce a forest, such that Σ_{F ∋ v} x_F >= 1 for every vertex v.

Conjecture 1.1: every planar graph G satisfies va_f(G) <= 2.

Encoding.  Graphs are finite and simple.  Planarity is defined by excluded minors (Wagner's
theorem).  "va_f(G) <= 2" means that, for some b >= 1, there are 2b sets inducing forests
(repetitions are allowed) such that every vertex is in at least b of them.  This is equivalent,
since the linear program has rational coefficients and hence a rational optimal solution. *)

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

(** The fractional vertex-arboricity of [G] is at most 2: for some [b >= 1], every vertex is
    covered at least [b] times by [2 * b] sets inducing forests. *)
Definition frac_vertex_arboricity_le2 (G : sgraph) : Prop :=
  exists b : nat,
    0 < b /\
    exists F : 'I_(2 * b) -> {set G},
      (forall i : 'I_(2 * b), is_forest (F i)) /\
      (forall v : G, b <= #|[set i : 'I_(2 * b) | v \in F i]|).

(** ** Statement *)

Definition AX_planar_fractional_vertex_arboricity_2 : Prop :=
  forall G : sgraph, planar G -> frac_vertex_arboricity_le2 G.
