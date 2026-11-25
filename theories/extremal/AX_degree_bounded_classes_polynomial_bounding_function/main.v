(** * Polynomial bounding functions for degree-bounded classes

Du, Girão, Hunter, McCarty, Scott, "Induced C_4-free subgraphs with large average degree",
arXiv:2307.08361 (2307.08361__00).

Let d(G) be the average degree of a graph G, and let τ(G) be its biclique number: the largest s
such that K_(s,s) is a subgraph, not necessarily induced, of G.  A hereditary class F (closed
under isomorphism and induced subgraphs) is degree-bounded if there is a function g such that
d(G) <= g(τ(G)) for every G in F.

Problem: is there, for every hereditary degree-bounded class F, a polynomial g such that
d(G) <= g(τ(G)) for every G in F?  The proposition states a positive answer.

Encoding.  d(G) is 2|E(G)|/|V(G)|, and the inequalities are multiplied by |V(G)|.  The function g
and the polynomial g have values and coefficients in nat, which is not a restriction for upper
bounds on nat.  The polynomial is the list [p] of its coefficients, and [horner_rec p t] is its
value at t. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between (G : sgraph) (A B : {set G}) : bool :=
  [forall a in A, [forall b in B, a -- b]].

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** A class of graphs is closed under taking induced subgraphs on subsets of vertices. *)
Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

(** A class of graphs is hereditary. *)
Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The largest [s] such that [G] has a subgraph [K_s,s], not necessarily induced. *)
Definition biclique_number (G : sgraph) : nat :=
  \max_(s < #|G|.+1 | [exists A : {set G}, exists B : {set G},
                         [&& #|A| == s, #|B| == s & complete_between A B]]) s.

(** The class [F] is degree-bounded: on its graphs, the average degree is bounded by a function
    of the biclique number. *)
Definition degree_bounded (F : sgraph -> Prop) : Prop :=
  exists g : nat -> nat, forall G : sgraph, F G -> 2 * #|E(G)| <= #|G| * g (biclique_number G).

(** ** Statement *)

Definition AX_degree_bounded_classes_polynomial_bounding_function : Prop :=
  forall F : sgraph -> Prop, hereditary_class F -> degree_bounded F ->
    exists p : seq nat, forall G : sgraph, F G ->
      2 * #|E(G)| <= #|G| * horner_rec p (biclique_number G).
