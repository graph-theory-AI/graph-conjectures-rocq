(** * Fractional chromatic number of planar triangle-free graphs

Dvořák, Masařík, Musílek, Pangrác, "Triangle-free planar graphs with the smallest independence
number", arXiv:1606.06265 (1606.06265__00).

For a positive integer b, a b-fold colouring of a graph G with a colours gives to each vertex a set
of b colours, such that adjacent vertices receive disjoint sets.  The fractional chromatic number
χ_f(G) is the minimum of a/b over these colourings.

Conjecture (suggested by the authors): every planar triangle-free graph G with n vertices satisfies
χ_f(G) <= 3 - 3/(n+1).

Encoding.  Graphs are finite and simple.  Planarity is the absence of minors K_5 and K_3,3.
Triangle-free means of girth at least 4.  The bound is written 3n/(n+1).  "χ_f(G) <= p/q" means
that there is a b-fold colouring with a colours such that a q <= p b. *)

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

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** ** Statement *)

Definition AX_triangle_free_planar_fractional_chromatic_bound : Prop :=
  forall G : sgraph,
    planar G -> girth_ge G 4 -> fractional_chromatic_le G (3 * #|G|) (#|G|).+1.
