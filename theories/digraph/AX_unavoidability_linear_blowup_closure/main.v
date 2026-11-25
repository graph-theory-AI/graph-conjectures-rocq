(** * Linear unavoidability of the blow-ups of a linearly unavoidable family

Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, "Blow-ups and extensions of trees in
tournaments", 2024, arXiv:2410.23566, Conjecture 7 (2410.23566__01).

A digraph D is p-unavoidable if every tournament on p vertices contains D as a (not necessarily
induced) subdigraph.  The unavoidability unvd(D) is the least such p; it exists if and only if D is
acyclic.  A family F of digraphs is linearly unavoidable if there is a constant C such that
unvd(D) <= C|V(D)| for every D in F.  The maximum average degree of a digraph is the maximum of
2|A(H)|/|V(H)| over its nonempty subdigraphs H.  For a positive integer k, the k-blow-up D[k] is
obtained from D by replacing each vertex by an independent set of k vertices, with arcs from all the
copies of u to all the copies of v for every arc uv of D, and F[k] is the family of the D[k] for D
in F.

Conjecture 7: if F is linearly unavoidable and has bounded maximum average degree, then F[k] is also
linearly unavoidable (for every k).

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]), and a family is a predicate [C] on them.  F[k] is closed under isomorphism.
"unvd(D) = N" is the relation [unavoidability_number D N].  Digraphs without unavoidability are
ignored in [linearly_unavoidable], which is harmless: the digraphs of F that are not acyclic have
blow-ups that are not acyclic.  The formal definition of D[k] in the source has arcs between copies
(u,i) and (v,j) for i <> j only; we take it as a misprint, as it is contradicted by the values given
there for the maximum average degree of blow-ups. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** Maximum average degree: the maximum of 2|A(S)|/|S| over nonempty [S] (0 if [D] is empty). *)
Definition digraph_mad (D : diGraph) : rat :=
  (\big[Num.max/0]_(S in [set S : {set D} | S != set0])
     ((2 * num_edges (induced S))%:Q / (#|S|)%:Q))%R.

(** Blow-up: each vertex is replaced by [k] copies without arcs between them. *)
Definition digraph_blowup (D : diGraph) (k : nat) : diGraph :=
  DiGraph (fun a b : D * 'I_k => a.1 -- b.1).

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** Each tournament on [N] vertices contains [D]. *)
Definition tournament_unavoidable (D : diGraph) (N : nat) : Prop :=
  forall T : diGraph, tournament T -> #|T| = N -> subdigraph D T.

(** [N] is the least number such that each tournament on [N] vertices contains [D]. *)
Definition unavoidability_number (D : diGraph) (N : nat) : Prop :=
  tournament_unavoidable D N /\ (forall M : nat, M < N -> ~ tournament_unavoidable D M).

(** The unavoidability number is at most linear in the number of vertices in the class [C]
    (digraphs without unavoidability number are ignored). *)
Definition linearly_unavoidable (C : diGraph -> Prop) : Prop :=
  exists c : nat, forall (D : diGraph) (N : nat),
    C D -> unavoidability_number D N -> (N <= c * #|D|)%N.

(** ** Definitions specific to the conjecture *)

(** F[k]: the digraphs isomorphic to the [k]-blow-up of a digraph of the family [C]. *)
Definition blowup_family (k : nat) (C : diGraph -> Prop) (E : diGraph) : Prop :=
  exists D : diGraph, C D /\ inhabited (E ≃ digraph_blowup D k).

(** ** Statement *)

Definition AX_unavoidability_linear_blowup_closure : Prop :=
  forall (C : diGraph -> Prop) (k : nat), 0 < k ->
    linearly_unavoidable C ->
    (exists a : nat, forall D : diGraph, C D -> (digraph_mad D <= a%:R)%R) ->
    linearly_unavoidable (blowup_family k C).
