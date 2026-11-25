(** * Decomposition of k-arc-strong tournaments into k spanning strong digraphs

Bang-Jensen, Yeo, "Decomposing k-arc-strong tournaments into strong spanning subdigraphs",
Combinatorica 24 (2004); Open Problem Garden,
decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs.

A digraph D is strong if every vertex has a directed path to every other.  It is k-arc-strong
if at least k arcs leave every nonempty proper subset of V(D), that is, if D remains strong
when fewer than k arcs are deleted.  D decomposes into k spanning strong digraphs if its arc
set can be partitioned into k sets A_1, ..., A_k such that every digraph (V(D),A_i) is strong.

Conjecture: every k-arc-strong tournament decomposes into k spanning strong digraphs.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with a
boolean relation [--]) satisfying the predicate [tournament].  The integer k is positive, which
is implicit in the source.  A partition of the arcs is given by a function [c] that assigns
to each arc the index of its part (its values on the other couples of vertices do not matter).
A tournament with at most one vertex is k-arc-strong for every k, and it trivially satisfies
the conclusion, with empty parts. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

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

Definition OPG_arc_strong_tournament_spanning_strong_decomposition : Prop :=
  forall (T : diGraph) (k : nat), tournament T -> 0 < k -> arc_strong T k ->
    exists c : T * T -> 'I_k, forall i : 'I_k, spanning_strong [set p in arcs T | c p == i].
