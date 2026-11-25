(** * Arc-disjoint directed cycles in regular digraphs

Alon, McDiarmid, Molloy, "Edge-disjoint cycles in regular directed graphs", J. Graph Theory 22
(1996); Open Problem Garden, arc_disjoint_directed_cycles_in_regular_directed_graphs.

A digraph is k-regular if every vertex has in-degree k and out-degree k.

Conjecture: if D is a k-regular digraph without parallel arcs, then D contains a collection of
(k+1 choose 2) arc-disjoint directed cycles.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--], hence without parallel arcs.  The digraph is nonempty.  Digons and loops are allowed,
and they are directed cycles.  "At least (k+1 choose 2) cycles" is the same as "exactly". *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** [D] is [d]-diregular: all in-degrees and out-degrees are equal to [d]. *)
Definition diregular (D : diGraph) (d : nat) : bool :=
  [forall v : D, (outdeg v == d) && (indeg v == d)].

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The arcs of the directed cycle [c]. *)
Definition dicycle_arcs (D : diGraph) (c : seq D) : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** ** Statement *)

Definition OPG_regular_digraph_arc_disjoint_cycles : Prop :=
  forall (D : diGraph) (k : nat), 0 < #|D| -> diregular D k ->
    exists P : seq (seq D),
      [/\ all (@dicycle D) P,
          pairwise (fun a b => [disjoint dicycle_arcs a & dicycle_arcs b]) P &
          'C(k.+1, 2) <= size P].
