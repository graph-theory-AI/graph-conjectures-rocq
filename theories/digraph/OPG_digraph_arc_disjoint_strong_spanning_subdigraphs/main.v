(** * Arc-disjoint strongly connected spanning subdigraphs

Bang-Jensen, Yeo, "Decomposing k-arc-strong tournaments into strong spanning subdigraphs",
Combinatorica 24 (2004); Open Problem Garden,
arc_disjoint_strongly_connected_spanning_subdigraphs.

A digraph D is k-arc-strong (or k-arc-connected) if at least k arcs leave every nonempty proper
subset of V(D), that is, if D remains strongly connected when fewer than k arcs are deleted.

Conjecture: there is an integer k such that every k-arc-strong digraph contains a pair of
arc-disjoint strongly connected spanning subdigraphs.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and so are loops, which play no role here.  Parallel arcs are
not represented, which is no restriction: each vertex of a digraph with parallel arcs can be
replaced by a large complete digraph, so that no two arcs have the same ends.  A spanning subdigraph
is given by its set of arcs.  A digraph with a single vertex is k-arc-strong for every k, and it
trivially satisfies the conclusion, with subdigraphs that have no arc. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** The arcs from [B] to its complement. *)
Definition outcut (D : diGraph) (B : {set D}) : {set D * D} :=
  [set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 -- p.2]].

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-arc-strong: at least [k] arcs leave each nonempty proper set of vertices (always
    true if [D] has at most one vertex). *)
Definition arc_strong (D : diGraph) (k : nat) : bool :=
  [forall B : {set D}, ((B != set0) && (B != [set: D])) ==> (k <= #|outcut B|)].

(** The arcs of [A] form a strongly connected spanning subdigraph of [D]. *)
Definition spanning_strong (D : diGraph) (A : {set D * D}) : Prop :=
  A \subset arcs D /\ strongly_connected (digraph_of_arcs A).

(** ** Statement *)

Definition OPG_digraph_arc_disjoint_strong_spanning_subdigraphs : Prop :=
  exists k : nat, forall D : diGraph, arc_strong D k ->
    exists A1 A2 : {set D * D}, [/\ [disjoint A1 & A2], spanning_strong A1 & spanning_strong A2].
