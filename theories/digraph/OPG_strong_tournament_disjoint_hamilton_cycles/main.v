(** * Edge-disjoint Hamilton cycles in highly connected tournaments

Thomassen, "Edge-disjoint Hamiltonian paths and cycles in tournaments", Proc. London Math. Soc. 45
(1982); Open Problem Garden, edge_disjoint_hamilton_cycles.

A digraph is strongly m-connected if it has more than m vertices and remains strongly connected when
fewer than m vertices are deleted.

Conjecture: for every k >= 2, there is an integer f(k) such that every strongly f(k)-connected
tournament has k edge-disjoint Hamilton cycles.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Directed cycles are given by the sequences of their vertices. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The arcs of the directed cycle [c]. *)
Definition dicycle_arcs (D : diGraph) (c : seq D) : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** [c] is a Hamiltonian directed cycle. *)
Definition hamiltonian_dicycle (D : diGraph) (c : seq D) : bool := dicycle c && (size c == #|D|).

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-strong: it has more than [k] vertices, and it remains strongly connected when
    fewer than [k] vertices are deleted. *)
Definition kstrong (D : diGraph) (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongly_connected (induced (~: S))].

(** ** Statement *)

Definition OPG_strong_tournament_disjoint_hamilton_cycles : Prop :=
  forall k : nat, 2 <= k ->
    exists m : nat,
      forall T : diGraph, tournament T -> kstrong T m ->
        exists P : seq (seq T),
          [/\ all (@hamiltonian_dicycle T) P,
              pairwise (fun a b => [disjoint dicycle_arcs a & dicycle_arcs b]) P &
              size P = k].
