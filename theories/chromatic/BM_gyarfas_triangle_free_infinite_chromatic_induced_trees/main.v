(** * Induced trees in triangle-free graphs of infinite chromatic number

Gyárfás; Bondy, Murty, "Graph Theory", Appendix A, problem 50.

Conjecture: every triangle-free graph of infinite chromatic number contains every finite tree as an
induced subgraph.

The proposition states the finite form: for every finite tree T, there is a constant c such that
every finite triangle-free graph that does not contain T as an induced subgraph has chromatic number
at most c.

Encoding.  Graphs are finite and simple.  The finite form is equivalent to the conjecture.  If it
holds, then the finite induced subgraphs of a triangle-free graph that does not contain T have
chromatic number at most c, hence so does this graph by the theorem of de Bruijn and Erdős.  If it
fails for T, then the disjoint union of finite triangle-free graphs of unbounded chromatic number
that do not contain T is a counterexample to the conjecture, since T is connected. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** ** Statement *)

Definition BM_gyarfas_triangle_free_infinite_chromatic_induced_trees : Prop :=
  forall T : sgraph,
    is_tree [set: T] ->
    exists c : nat,
      forall G : sgraph,
        triangle_free G -> ~ has_induced_copy G T -> χ([set: G]) <= c.
