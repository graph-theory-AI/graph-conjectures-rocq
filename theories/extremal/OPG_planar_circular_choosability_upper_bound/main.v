(** * Circular choosability of planar graphs

Mohar (2003); Havet, Kang, Müller, Sereni, "Circular choosability", J. Graph Theory 61 (2009);
Open Problem Garden, circular_choosability_of_planar_graphs.

A (p,q)-colouring of a graph gives to each vertex a colour in {0, ..., p-1} such that
q <= |i - j| <= p - q for the colours i and j of any two adjacent vertices.  A graph G is circularly
t-choosable if, for all p and q and all lists L(v) of at least tq elements of {0, ..., p-1}, it has
a (p,q)-colouring with the colour of each vertex v in L(v).  The circular choosability cch(G) is the
infimum of the t >= 1 such that G is circularly t-choosable.

Problem: what is the best upper bound on cch(G) for planar graphs G?

The proposition only states that this bound, the least upper bound of cch(G) for planar graphs G,
is a rational number between 6 and 8 (Havet, Kang, Müller and Sereni proved that it is between 6
and 8).

Encoding.  The problem suggests no value: the proposition is a proxy, weaker than a determination
of the bound (as a rational number).  Graphs are finite and simple, and planarity is expressed by
excluded minors (Wagner's theorem).  The inequality cch(G) <= B is expressed as: G is circularly
t-choosable for all rational t > B. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [c] is a circular [(p,q)]-colouring: its values are less than [p] and, for adjacent
    vertices, they differ by at least [q] and at most [p - q]. *)
Definition circular_coloring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v))%R)%N /\
     (absz (Posz (c u) - Posz (c v))%R <= p - q)%N).

(** [G] is circularly [t]-choosable: for all [p] and [q], it has a circular [(p,q)]-colouring
    from all lists of size at least [t * q]. *)
Definition circularly_choosable (G : sgraph) (t : rat) : Prop :=
  forall p q : nat, (0 < q)%N ->
    forall L : G -> {set 'I_p},
      (forall v, (t * q%:Q <= (#|L v|)%:Q)%R) ->
      exists c : G -> 'I_p,
        circular_coloring (fun x y : G => x -- y) p q (fun v => (c v : nat)) /\
        (forall v, c v \in L v).

(** ** Definitions specific to the conjecture *)

(** cch(G) <= B for all planar graphs G. *)
Definition planar_circular_choosability_le (B : rat) : Prop :=
  forall G : sgraph, planar G -> forall t : rat, (B < t)%R -> circularly_choosable G t.

(** ** Statement *)

Definition proxy_OPG_planar_circular_choosability_upper_bound : Prop :=
  exists B : rat,
    [/\ 6%:Q <= B <= 8%:Q, planar_circular_choosability_le B
      & forall B' : rat, planar_circular_choosability_le B' -> B <= B']%R.
