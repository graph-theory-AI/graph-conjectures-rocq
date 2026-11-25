(** * Exact colourings of the infinite complete graph

Erickson, "A conjecture concerning Ramsey's theorem", Discrete Mathematics 126 (1994), 395-398;
Open Problem Garden, exact_colorings_of_graphs.

An exact c-colouring of the edges of a graph is a colouring with c colours all of which are used
at least once.  For c >= m >= 1, let P(c,m) be the statement that, for every exact c-colouring of
the edges of the complete graph on countably many vertices, there is a complete subgraph on
infinitely many vertices whose edges have exactly m colours.

Conjecture: P(c,m) is true if and only if m = 1, m = 2 or c = m.

Encoding.  The vertices are the natural numbers.  A colouring is a symmetric function of two
vertices, whose values on the diagonal are never used.  The complete subgraph is given by an
injective sequence of vertices. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** A colouring of the edges of the complete graph on [nat] ([col x x] is irrelevant). *)
Definition edge_coloring_nat (c : nat) : Type := nat -> nat -> 'I_c.

Definition symmetric_coloring (c : nat) (col : edge_coloring_nat c) : Prop :=
  forall x y, col x y = col y x.

(** All colours are used. *)
Definition exact_coloring (c : nat) (col : edge_coloring_nat c) : Prop :=
  forall k : 'I_c, exists x y, x <> y /\ col x y = k.

(** The colour [k] is used between two vertices of the sequence [s]. *)
Definition uses_color (c : nat) (col : edge_coloring_nat c) (s : nat -> nat) (k : 'I_c) : Prop :=
  exists i j, i <> j /\ col (s i) (s j) = k.

(** Exactly [m] colours are used between the vertices of the sequence [s]. *)
Definition exactly_m_colored (c : nat) (col : edge_coloring_nat c) (s : nat -> nat) (m : nat) :
    Prop :=
  exists T : {set 'I_c}, #|T| = m /\ forall k, (k \in T) <-> uses_color col s k.

(** The property P(c,m). *)
Definition exact_subgraph_property (c m : nat) : Prop :=
  forall col : edge_coloring_nat c,
    symmetric_coloring col -> exact_coloring col ->
    exists s : nat -> nat, injective s /\ exactly_m_colored col s m.

(** ** Statement *)

Definition OPG_exact_edge_coloring_infinite_complete_subgraph : Prop :=
  forall c m : nat, 1 <= m -> m <= c ->
    (exact_subgraph_property c m <-> (m = 1 \/ m = 2 \/ c = m)).
