(** * 2-colourings without monochromatic maximum clique

Hoàng, McDiarmid, "On the divisibility of graphs", Discrete Mathematics 242 (2002);
Bondy, Murty, "Graph Theory", unsolved problem 49;
Open Problem Garden, 2_colouring_a_graph_without_a_monochromatic_maximum_clique.

A maximum clique of a graph G is a clique of maximum cardinality ω(G).

Conjecture: if G is a nonempty graph that contains no induced odd cycle of length at least 5,
then its vertices can be coloured with two colours in such a way that no maximum clique is
monochromatic.

Encoding.  The colourings are arbitrary maps to the booleans.  "Nonempty" means that G has at
least one edge: the maximum cliques of an edgeless graph are its vertices, which are always
monochromatic. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
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

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/chromatic.v *)

(** All elements of [S] have the same colour. *)
Definition monochromatic_on (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) : bool :=
  constant [seq col x | x <- enum S].

(** ** Definitions specific to the conjecture *)

(** No maximum clique of [G] is monochromatic. *)
Definition splits_max_cliques (G : sgraph) (c : G -> bool) : Prop :=
  forall Q : {set G}, Q \in maxcliques [set: G] -> ~ monochromatic_on c Q.

(** ** Statement *)

Definition OPG_odd_hole_free_nonmonochromatic_max_cliques : Prop :=
  forall G : sgraph,
    (exists x y : G, x -- y) ->
    (forall k : nat, odd k -> 5 <= k -> ~ has_induced_copy G (cycle_graph k)) ->
    exists c : G -> bool, splits_max_cliques c.
