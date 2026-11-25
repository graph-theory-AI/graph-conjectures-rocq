(** * Non-edges versus feedback arc sets in digraphs

Chudnovsky, Seymour, Sullivan, "Cycles in dense digraphs", Combinatorica 28 (2008);
Open Problem Garden, non_edges_vs_feedback_edge_sets_in_digraphs.

For a digraph G, γ(G) is the number of unordered pairs of nonadjacent vertices, and β(G) is the
minimum size of a feedback arc set, i.e., of a set of arcs whose deletion leaves a digraph
without directed cycle.

Conjecture: if G is a simple digraph without directed cycles of length at most 3, then
β(G) <= γ(G) / 2.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Loops and digons are directed cycles of length 1 and 2, hence excluded
by the hypothesis.  The inequality is multiplied by 2. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Deletion of the arcs of [F]. *)
Definition del_arcs (D : diGraph) (F : {set D * D}) : diGraph :=
  DiGraph (fun u v : D => (u -- v) && ((u, v) \notin F)).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The directed girth of [D] is larger than [r]. *)
Definition digirth_gt (D : diGraph) (r : nat) : Prop :=
  forall c : seq D, dicycle c -> (r < size c)%N.

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The minimum size of a set of arcs that meets all directed cycles. *)
Definition feedback_arc_number (D : diGraph) : nat :=
  #|[arg min_(F < [set: D * D] | acyclic (del_arcs F)) #|F|]|.

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** ** Definitions specific to the conjecture *)

(** The number of unordered pairs of distinct nonadjacent vertices. *)
Definition num_non_edges (D : diGraph) : nat :=
  #|[set e : {set D} | (#|e| == 2) && arc_free e]|.

(** ** Statement *)

Definition OPG_digraph_feedback_arcs_vs_non_edges : Prop :=
  forall D : diGraph, digirth_gt D 3 -> 2 * feedback_arc_number D <= num_non_edges D.
