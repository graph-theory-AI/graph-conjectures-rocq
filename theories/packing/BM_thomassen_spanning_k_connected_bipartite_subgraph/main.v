(** * Spanning k-connected oriented subgraphs of 2k-connected digraphs

Thomassen (1989); Bondy, Murty, "Graph Theory", Appendix A (French edition by Havet), problem 25
(bm-025).

A digraph D is k-connected if it has more than k vertices and if D - S is strongly connected for
every set S of fewer than k vertices.  An oriented graph is a digraph without loops and without
pairs of opposite arcs.

Conjecture: for k >= 1, every 2k-connected digraph contains a spanning k-connected oriented
subgraph.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  D may have loops and pairs of opposite arcs; parallel arcs are not represented,
which does not matter here.  A spanning subgraph of D is given by its arc set A, a subset of the
arcs of D.  The canonical name refers to a similar problem on bipartite subgraphs of undirected
graphs; the conjecture of the book is the one stated here. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-strong: it has more than [k] vertices, and it remains strongly connected when
    fewer than [k] vertices are deleted. *)
Definition kstrong (D : diGraph) (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongly_connected (induced (~: S))].

(** ** Statement *)

Definition BM_thomassen_spanning_k_connected_bipartite_subgraph : Prop :=
  forall (k : nat) (D : diGraph),
    0 < k -> kstrong D (2 * k) ->
    exists A : {set D * D},
      [/\ A \subset arcs D, oriented (digraph_of_arcs A) & kstrong (digraph_of_arcs A) k].
