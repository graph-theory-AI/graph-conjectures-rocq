(** * Dense bipartite induced subgraphs of graphs of large girth

Esperet, Kang, Thomassé, "Separation choosability and dense bipartite induced subgraphs", Combin.
Probab. Comput. 28 (2019), arXiv:1802.03727, Conjecture 1.6 (1802.03727__03).

Conjecture: there exist d0 and g0 such that every graph of girth at least g0 with minimum degree at
least d0 contains a bipartite induced subgraph of minimum degree at least 3.

Encoding.  Graphs are finite, simple and nonempty, and so is the induced subgraph. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/extremal.v *)

(** [G] has a nonempty bipartite induced subgraph of minimum degree at least [d]. *)
Definition dense_bipartite_induced (G : sgraph) (d : nat) : Prop :=
  exists S : {set G}, [/\ S != set0, bipartite (induced S) & min_degree_ge (induced S) d].

(** ** Statement *)

Definition AX_dense_bipartite_induced_large_girth : Prop :=
  exists d0 g0 : nat, forall G : sgraph,
    0 < #|G| -> girth_ge G g0 -> min_degree_ge G d0 -> dense_bipartite_induced G 3.
