(** * Reconstruction

    The deck of a graph is the multiset of its vertex-deleted subgraphs, up to isomorphism;
    equality of decks is the existence of a bijection between the vertices such that
    corresponding cards are isomorphic.  Similarly for edges and for switchings. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [G] and [H] have the same deck (they are hypomorphic). *)
Definition same_deck (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall v : G, inhabited (induced [set~ v] ≃ induced [set~ f v]).

(** [G] is reconstructible from its deck. *)
Definition reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_deck G H -> inhabited (G ≃ H).

(** [G] and [H] have the same edge-deck. *)
Definition same_edge_deck (G H : sgraph) : Prop :=
  exists f : {e : {set G} | e \in E(G)} -> {e : {set H} | e \in E(H)},
    bijective f /\
    forall e : {e : {set G} | e \in E(G)},
      inhabited (del_edges (val e) ≃ del_edges (val (f e))).

(** [G] is reconstructible from its edge-deck. *)
Definition edge_reconstructible (G : sgraph) : Prop :=
  forall H : sgraph, same_edge_deck G H -> inhabited (G ≃ H).

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
