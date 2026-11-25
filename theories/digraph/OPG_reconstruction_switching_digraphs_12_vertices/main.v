(** * Switching reconstruction of digraphs

Bondy, Mercier, "Switching reconstruction of digraphs", J. Graph Theory 67 (2011); Open Problem
Garden, switching_reconstruction_of_digraphs.

To switch a vertex of a digraph is to reverse all the arcs incident to it.  The switching deck of a
digraph D is the multiset of the digraphs obtained by switching a vertex of D, up to isomorphism.
D is switching-reconstructible if every digraph with the same switching deck is isomorphic to D.

Question: are there any switching-nonreconstructible digraphs on twelve or more vertices?  The
proposition states a negative answer, for oriented graphs (digraphs without loop and without digon):
every oriented graph on at least twelve vertices is switching-reconstructible.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Loops and digons, which switching does not change, are excluded: McKay and
Schweitzer ("Switching reconstruction of digraphs", J. Graph Theory 76, 2014) report the question of
Bondy and Mercier for oriented graphs, and give two non-isomorphic digraphs with digons on twelve
vertices that have the same deck.  Equality of decks is the existence of a bijection between the
vertices such that the corresponding switchings are isomorphic. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** Switching: reversal of the arcs with exactly one end in [S]. *)
Definition digraph_switch (D : diGraph) (S : {set D}) : diGraph :=
  DiGraph (fun u v : D => if (u \in S) (+) (v \in S) then v -- u else u -- v).

(** ** Definitions specific to the conjecture *)

(** [D] and [D'] have the same switching deck. *)
Definition digraph_same_switching_deck (D D' : diGraph) : Prop :=
  exists f : D -> D',
    bijective f /\
    forall v : D, inhabited (digraph_switch [set v] ≃ digraph_switch [set f v]).

(** [D] is reconstructible from its switching deck. *)
Definition digraph_switching_reconstructible (D : diGraph) : Prop :=
  forall D' : diGraph, digraph_same_switching_deck D D' -> inhabited (D ≃ D').

(** ** Statement *)

Definition OPG_reconstruction_switching_digraphs_12_vertices : Prop :=
  forall D : diGraph, oriented D -> 12 <= #|D| -> digraph_switching_reconstructible D.
