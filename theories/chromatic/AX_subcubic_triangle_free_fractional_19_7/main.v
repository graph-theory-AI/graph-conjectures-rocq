(** * Fractional 19/7-colourings of subcubic triangle-free graphs

Dvořák, Lidický, Postle, "11/4-colorability of subcubic triangle-free graphs", arXiv:2204.12683,
Conjecture 1.6 (2204.12683__00).

A graph is subcubic if its maximum degree is at most 3.  For positive integers a and b, an
(a:b)-colouring gives to each vertex b colours among a, such that adjacent vertices receive disjoint
sets.  A graph is fractionally k-colourable if it has an (a:b)-colouring with a/b <= k.

The paper defines by figures four subcubic triangle-free graphs: F14^(1) and F14^(2), on 14
vertices, of fractional chromatic number 14/5 (F14^(1) is the generalized Petersen graph P(7,2)),
and F11 and F22, on 11 and 22 vertices, of fractional chromatic number 11/4.

Conjecture 1.6: every subcubic triangle-free graph avoiding F14^(1), F14^(2), F11 and F22 as
subgraphs is fractionally 19/7-colourable.

Encoding.  Graphs are finite and simple.  Subgraphs are not necessarily induced.  The four graphs
are given by the lists of their edges, read off the figures of the paper. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** Every vertex has degree at most 3. *)
Definition subcubic (G : sgraph) : Prop := forall v : G, #|N(v)| <= 3.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** ** Definitions specific to the conjecture *)

(** F14^(1), the generalized Petersen graph P(7,2): the outer cycle is 0, ..., 6, the spokes join
    [i] to [7 + i], and the inner vertices [7 + i] and [7 + (i + 2 mod 7)] are adjacent. *)
Definition F14_1 : sgraph :=
  sgraph_of_rel (fun i j : 'I_14 => (val i, val j) \in
    [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 0);
        (0, 7); (1, 8); (2, 9); (3, 10); (4, 11); (5, 12); (6, 13);
        (7, 9); (9, 11); (11, 13); (13, 8); (8, 10); (10, 12); (12, 7)]).

(** F14^(2): a cycle 0, ..., 7 and the vertices 8, 9, 10 (z_1, z_2, z_3) and 11, 12, 13 (w_1, w_2,
    w_3) of the figure. *)
Definition F14_2 : sgraph :=
  sgraph_of_rel (fun i j : 'I_14 => (val i, val j) \in
    [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 0);
        (0, 8); (8, 9); (9, 12); (12, 11); (11, 7); (2, 9); (12, 5);
        (10, 1); (10, 11); (10, 4); (13, 6); (13, 8); (13, 3)]).

(** F11: the vertices are x_i = [i] and y_i = [4 + i] (i < 4), x_l = 8, x_r = 9 and y_t = 10. *)
Definition F11 : sgraph :=
  sgraph_of_rel (fun i j : 'I_11 => (val i, val j) \in
    [:: (8, 0); (0, 1); (1, 6); (6, 7); (7, 9); (9, 3); (3, 2); (2, 5); (5, 4); (4, 8);
        (8, 10); (10, 9); (1, 5); (2, 6); (0, 3); (4, 7)]).

(** F22: the vertices are x_i = [i], y_i = [5 + i], z_i = [10 + i], w_i = [15 + i] (i < 5), z = 20
    and w = 21. *)
Definition F22 : sgraph :=
  sgraph_of_rel (fun i j : 'I_22 => (val i, val j) \in
    [:: (0, 5); (1, 6); (2, 7); (3, 8); (4, 9);
        (5, 10); (6, 11); (7, 12); (8, 13); (9, 14);
        (10, 15); (11, 16); (12, 17); (13, 18); (14, 19);
        (0, 1); (1, 2); (2, 3); (3, 4);
        (10, 6); (11, 7); (12, 8); (13, 9);
        (15, 16); (16, 17); (17, 18); (18, 19);
        (5, 20); (20, 21); (21, 15);
        (19, 0); (14, 20); (4, 21)]).

(** ** Statement *)

Definition AX_subcubic_triangle_free_fractional_19_7 : Prop :=
  forall G : sgraph, subcubic G -> triangle_free G ->
    ~ subgraph F14_1 G -> ~ subgraph F14_2 G -> ~ subgraph F11 G -> ~ subgraph F22 G ->
    fractional_chromatic_le G 19 7.
