(** * Pebbling a cartesian product

Graham; F. Chung, "Pebbling in hypercubes", SIAM J. Disc. Math. 2 (1989); Open Problem Garden,
pebbling_a_cartesian_product.

A pebbling move removes two pebbles from a vertex and adds one pebble to an adjacent vertex.  The
pebbling number p(G) of a graph G is the smallest integer k such that, for every distribution of k
pebbles on the vertices, a pebble can be brought to any vertex by a sequence of pebbling moves.
In the cartesian product of G1 and G2, vertices are adjacent if they are equal in one coordinate
and adjacent in the other.

Conjecture: p(G1 □ G2) <= p(G1) p(G2).

Encoding.  Graphs are finite, simple and nonempty.  The pebbling number is a relation between G
and k, which holds for no k if G is not connected (the conjecture concerns connected graphs). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

End Products.

(** A pebbling move: two pebbles are removed from a vertex, and one is added to a neighbour. *)
Definition pebble_move (G : sgraph) (D D' : G -> nat) : Prop :=
  exists u v : G,
    [/\ u -- v, 2 <= D u &
        forall w : G, D' w = if w == u then D u - 2
                             else if w == v then D v + 1 else D w].

(** The distribution of pebbles [D'] is reached from [D] by pebbling moves. *)
Inductive pebble_reach (G : sgraph) : (G -> nat) -> (G -> nat) -> Prop :=
| pebble_reach_refl (D : G -> nat) : pebble_reach D D
| pebble_reach_step (D D' D'' : G -> nat) :
    pebble_move D D' -> pebble_reach D' D'' -> pebble_reach D D''.

(** Pebbling moves from [D] can bring a pebble to [r]. *)
Definition pebble_solvable (G : sgraph) (D : G -> nat) (r : G) : Prop :=
  exists D' : G -> nat, pebble_reach D D' /\ 1 <= D' r.

(** The pebbling number of [G] is [N]: the least number of pebbles such that a pebble can be
    brought to any vertex from any distribution. *)
Definition pebbling_number (G : sgraph) (N : nat) : Prop :=
  (forall D : G -> nat, \sum_(v : G) D v = N -> forall r : G, pebble_solvable D r) /\
  (forall M : nat,
     (forall D : G -> nat, \sum_(v : G) D v = M -> forall r : G, pebble_solvable D r) ->
     N <= M).

(** ** Statement *)

Definition OPG_graham_pebbling_cartesian_product : Prop :=
  forall (G1 G2 : sgraph) (p1 p2 p12 : nat),
    0 < #|G1| -> 0 < #|G2| ->
    pebbling_number G1 p1 ->
    pebbling_number G2 p2 ->
    pebbling_number (cartesian_product G1 G2) p12 ->
    p12 <= p1 * p2.
