(** * Fractional chromatic number of planar graphs without cycles of length 4 or 5

Dvořák, Hu, "Planar graphs without cycles of length 4 or 5 are (11:3)-colorable", arXiv:1802.04179
(1802.04179__01).

For positive integers b <= a, an (a:b)-colouring of a graph G gives to each vertex a set of b
colours among a, such that adjacent vertices receive disjoint sets.  The fractional chromatic
number χ_f(G) is the minimum of a/b over these colourings.

The authors prove that χ_f(G) <= 11/3 for every planar graph G without cycles of length 4 or 5,
and suspect that the constant 11/3 is not the best possible.

Conjecture: there is a constant c < 11/3 such that χ_f(G) <= c for every planar graph G without
cycles of length 4 or 5.

Encoding.  Graphs are finite and simple.  Planarity is the absence of K_5 and K_3,3 minors (Wagner's
theorem).  The constant c is a rational number p/q, without loss of generality.  "χ_f(G) <= p/q"
means that G has an (a:b)-colouring with b > 0 and a q <= p b. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** [G] has no cycle whose length is between [lo] and [hi]. *)
Definition no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> lo <= size c -> size c <= hi -> False.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition AX_planar_c4_c5_fractional_chromatic_11_3 : Prop :=
  exists p q : nat,
    [/\ 0 < q, 3 * p < 11 * q
      & forall G : sgraph,
          planar G -> no_cycle_length_between G 4 5 ->
          fractional_chromatic_le G p q].
