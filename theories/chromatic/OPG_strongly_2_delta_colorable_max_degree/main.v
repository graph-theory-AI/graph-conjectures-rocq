(** * Strong colourability

Aharoni, Alon, Haxell; Open Problem Garden, strong_colorability.

Let r be a positive integer.  A graph G is strongly r-colourable if, for every partition of its
vertices into sets of size at most r, G has a proper colouring with r colours in which the vertices
of each set of the partition have distinct colours.

Conjecture: every graph G of maximum degree Δ is strongly 2Δ-colourable.

Encoding.  Graphs are finite and simple.  Graphs without edges are excluded, as 2Δ must be
positive. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] is strongly [r]-colourable: for each partition of its vertices in parts of size at most
    [r], it has a proper [r]-colouring that is injective on the parts. *)
Definition strongly_colorable (G : sgraph) (r : nat) : Prop :=
  forall P : {set {set G}},
    partition P [set: G] -> (forall B : {set G}, B \in P -> #|B| <= r) ->
    exists f : G -> 'I_r,
      (forall x y : G, x -- y -> f x != f y) /\
      (forall B : {set G}, B \in P -> {in B &, injective f}).

(** ** Statement *)

Definition OPG_strongly_2_delta_colorable_max_degree : Prop :=
  forall G : sgraph, 0 < Delta G -> strongly_colorable G (2 * Delta G).
