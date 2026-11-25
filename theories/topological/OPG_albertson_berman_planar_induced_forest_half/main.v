(** * Large induced forests in planar graphs

Albertson, Berman, "A conjecture on planar graphs", in Graph Theory and Related Topics (Bondy,
Murty eds.), Academic Press, 1979, p. 357; Open Problem Garden,
large_induced_forest_in_a_planar_graph.

Conjecture: every planar graph on n vertices has an induced forest with at least n/2 vertices.

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3 (Wagner's
theorem). *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_albertson_berman_planar_induced_forest_half : Prop :=
  forall G : sgraph,
    planar G -> exists S : {set G}, is_forest S /\ #|G| <= 2 * #|S|.
