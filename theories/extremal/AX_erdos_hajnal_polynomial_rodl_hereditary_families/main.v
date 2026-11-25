(** * Polynomial close Rödl property of hereditary families

Bucić, Fox, Pham, "Equivalence between Erdős-Hajnal and polynomial Rödl and Nikiforov
conjectures", arXiv:2403.08303, Conjecture 10 (2403.08303__00).

A family of graphs is hereditary if it is closed under isomorphism and induced subgraphs, and
proper if it does not contain all graphs.  A set S of vertices of G is ε-homogeneous if the edge
density of G[S] is at most ε or at least 1-ε.  A graph G on n vertices is α-close to a family F if
one can add or delete at most αn^2/2 edges to obtain a graph in F.

Conjecture 10: for each proper hereditary family F of graphs, there are C, d > 0 such that, if
0 < ε < 1/2, every graph on n vertices which is ε^d-close to F contains an ε-homogeneous set of size
at least ε^C n.

Encoding.  ε is a rational number a/b, C and d are positive integers, and the inequalities are
multiplied by the denominators.  This is equivalent: C and d can be increased, and for each graph
the case of a real number ε follows from that of its upper rational approximations.  The sets with
at most one vertex are ε-homogeneous, which changes nothing: so are the sets with two vertices.
The edges that are added or deleted are counted as ordered pairs, hence twice. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** A class of graphs is closed under taking induced subgraphs on subsets of vertices. *)
Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

(** A class of graphs is hereditary. *)
Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

(** ** Definitions specific to the conjecture *)

(** [G] is ([a] / [b])-close to [F]: some graph of [F] with the same vertices differs from it on at
    most [(a / b) #|G| ^ 2] ordered pairs of vertices. *)
Definition close_to (F : sgraph -> Prop) (G : sgraph) (a b : nat) : Prop :=
  exists (r : rel G) (rs : symmetric r) (ri : irreflexive r),
    F (SGraph rs ri) /\ b * #|[set p : G * G | (p.1 -- p.2) != r p.1 p.2]| <= a * #|G| ^ 2.

(** [S] is ([a] / [b])-homogeneous. *)
Definition eps_homogeneous (G : sgraph) (a b : nat) (S : {set G}) : Prop :=
  b * #|E(induced S)| <= a * 'C(#|S|, 2) \/
  (b - a) * 'C(#|S|, 2) <= b * #|E(induced S)|.

(** ** Statement *)

Definition AX_erdos_hajnal_polynomial_rodl_hereditary_families : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> (exists G0 : sgraph, ~ F G0) ->
    exists C d : nat, [/\ 0 < C, 0 < d &
      forall (a b : nat) (G : sgraph), 0 < a -> 2 * a < b ->
        close_to F G (a ^ d) (b ^ d) ->
        exists S : {set G}, eps_homogeneous a b S /\ a ^ C * #|G| <= b ^ C * #|S|].
