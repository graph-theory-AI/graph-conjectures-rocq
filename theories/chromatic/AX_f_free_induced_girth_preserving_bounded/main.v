(** * Graphs of given girth whose F-free induced subgraphs have bounded chromatic number

Girão, Illingworth, Powierski, Savery, Scott, Tamitegama, Tan, "Induced subgraphs of induced
subgraphs of large chromatic number", arXiv:2203.03612, Girth Conjecture (2203.03612__00).

A graph G is F-free if it has no induced subgraph isomorphic to F.

Conjecture: for every triangle-free graph F, there is a constant c_F and graphs G of arbitrarily
large chromatic number and the same girth as F such that every F-free induced subgraph of G is
c_F-colourable.

Encoding.  Graphs are finite and simple.  The graph F is assumed to have a cycle: for a forest F,
a graph G of the same (infinite) girth would be a forest too. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** The girth of [G] is [g]. *)
Definition girth (G : sgraph) (g : nat) : Prop :=
  girth_ge G g /\ (exists c : seq G, seq_cycle (--) c /\ size c = g).

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** ** Definitions specific to the conjecture *)

(** [G] and [H] have the same girth (or no cycle). *)
Definition same_girth (G H : sgraph) : Prop :=
  forall g : nat, girth G g <-> girth H g.

(** ** Statement *)

Definition AX_f_free_induced_girth_preserving_bounded : Prop :=
  forall F : sgraph,
    triangle_free F ->
    (exists g : nat, girth F g) ->
    exists cF : nat, forall m : nat,
      exists G : sgraph,
        [/\ m <= χ([set: G]),
            same_girth F G
          & forall S : {set G}, induced_free (induced S) F -> χ([set: induced S]) <= cF].
