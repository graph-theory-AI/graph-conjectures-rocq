(** * Polynomial bounds for path-induced copies of rooted trees

Nguyen, Scott, Seymour, "A note on the Gyárfás–Sumner conjecture", arXiv:2302.08922
(2302.08922__00).

A path-induced copy of a rooted tree (T,r) in a graph G is an isomorphism from T to a (not
necessarily induced) subgraph of G such that the image of every path of T with one end r is an
induced path of G.

Question: is the chromatic number of the graphs with no path-induced copy of a rooted tree (T,r) and
with clique number at most t bounded by a polynomial in t?

The proposition states the positive answer, for all (T,r).

Encoding.  Graphs are finite and simple.  The chromatic number is bounded by a polynomial in the
clique number, which is equivalent.  The polynomial has the form f(t) = c t^d, without loss of
generality. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** ** Definitions specific to the conjecture *)

(** Non-consecutive vertices of the sequence [s] are not adjacent (with default value [x0]). *)
Definition induced_run (G : sgraph) (x0 : G) (s : seq G) : Prop :=
  forall i j : nat, j < size s -> i.+1 < j -> ~~ (nth x0 s i -- nth x0 s j).

(** [G] has a path-induced copy of the rooted tree [(T, r)].  A path of [T] with one end [r] is
    represented by [r :: p]. *)
Definition path_induced_copy (T : sgraph) (r : T) (G : sgraph) : Prop :=
  exists phi : T -> G,
    [/\ injective phi,
        (forall x y : T, x -- y -> phi x -- phi y) &
        (forall p : seq T, path (--) r p -> uniq (r :: p) ->
           induced_run (phi r) (map phi (r :: p)))].

(** ** Statement *)

Definition AX_path_induced_rooted_tree_polynomial_chi : Prop :=
  forall (T : sgraph) (r : T),
    is_tree [set: T] ->
    poly_chi_bounded (fun G : sgraph => ~ path_induced_copy r G).
