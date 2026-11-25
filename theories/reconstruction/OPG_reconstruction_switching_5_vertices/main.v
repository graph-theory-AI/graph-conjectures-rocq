(** * Switching reconstruction conjecture

Stanley, "Reconstruction from vertex-switching", J. Combin. Theory B 38 (1985); Open Problem
Garden, switching_reconstruction_conjecture.

To switch a vertex of a simple graph is to exchange its sets of neighbours and non-neighbours.
The switching deck of G is the multiset of the graphs obtained from G by switching one vertex, up
to isomorphism.  G is switching-reconstructible if every graph with the same switching deck as G is
isomorphic to G.

Conjecture: every simple graph with at least 5 vertices is switching-reconstructible.

Encoding.  Graphs are finite.  Two graphs have the same switching deck if there is a bijection f
between their vertex sets such that G switched at v is isomorphic to H switched at f(v) for every
vertex v of G. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/reconstruction.v *)

Section Switch.
Variables (G : sgraph) (S : {set G}).

(** The edges of [G], complemented between [S] and the other vertices. *)
Definition switch_rel : rel G := fun x y => (x -- y) (+) ((x \in S) (+) (y \in S)).

Lemma switch_sym : symmetric switch_rel.
Proof. by move=> x y; rewrite /switch_rel sg_sym [(x \in S) (+) _]addbC. Qed.

Lemma switch_irrefl : irreflexive switch_rel.
Proof. by move=> x; rewrite /switch_rel sg_irrefl addbb. Qed.

(** The (Seidel) switching of [G] with respect to [S]. *)
Definition seidel_switch : sgraph := SGraph switch_sym switch_irrefl.

End Switch.

(** [G] and [H] have the same deck of switchings at one vertex. *)
Definition same_switching_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (seidel_switch [set v] ≃ seidel_switch [set f v]).

(** [G] is reconstructible from its switching deck. *)
Definition switching_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_switching_deck G H -> inhabited (G ≃ H).

(** ** Statement *)

Definition OPG_reconstruction_switching_5_vertices : Prop :=
  forall G : sgraph, 5 <= #|G| -> switching_reconstructible G.
