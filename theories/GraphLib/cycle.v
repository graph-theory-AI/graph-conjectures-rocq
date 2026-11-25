(** * Cycles, cycle covers and decompositions, flows

Multigraphs have loops and parallel edges, and degrees [mdeg], [mdeg_in] where a loop is
counted twice.  Cycles of multigraphs are sets of edges ([is_circuit]); the reference direction
of the edges (from [source] to [target]) is arbitrary.  Cycles of simple graphs are sequences of
vertices ([seq_cycle]). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph coloring connectivity.
From GraphTheory Require skeleton.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc chromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Degrees in multigraphs *)

(** [G] is of class 1: its chromatic index is equal to its maximum degree ([G] has no loop). *)
Definition class_one (G : mgraph) : Prop := mchromatic_index G = mDelta G.

(** [G] is eulerian: it is connected (possibly empty) and all degrees are even. *)
Definition eulerian (G : mgraph) : Prop :=
  connected [set: skeleton.skeleton G] /\ forall v : G, ~~ odd (mdeg v).

(** [w] is an eulerian tour: a closed walk that uses every edge exactly once. *)
Definition eulerian_tour (G : mgraph) (w : seq (edge G)) : Prop :=
  (exists x : G, uwalk x x w) /\ (forall e : edge G, count (pred1 e) w = 1).

(** ** Sets of edges of multigraphs *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types (C F H P S T : {set edge G}).

(** [F] is the edge set of a 2-factor. *)
Definition two_factor F : Prop :=
  forall v : G, mdeg_in F v = 2.

(** [C] is an even subgraph: all its degrees are even. *)
Definition even_subgraph C : Prop :=
  forall v : G, ~~ odd (mdeg_in C v).

(** [H] contains no cycle. *)
Definition acyclic_edge_set H : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** [P] is the edge set of a path with at least one edge. *)
Definition path_subgraph P : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic_edge_set P & forall v : G, (mdeg_in P v <= 2)%N].

(** The spanning subgraph with edge set [T] is connected. *)
Definition spanning_connected T : Prop :=
  connected [set: skeleton.skeleton (remove_edges (~: T))].

(** [T] is the edge set of a spanning tree. *)
Definition mspanning_tree T : Prop :=
  spanning_connected T /\ acyclic_edge_set T.

(** The spanning subgraph with edge set [S] is [a]-edge-connected. *)
Definition spanning_edge_connected S (a : nat) : Prop :=
  forall F : {set edge G}, F \subset S -> #|F| < a -> spanning_connected (S :\: F).

(** [T] is a cut with an odd number of edges. *)
Definition odd_edge_cut T : Prop :=
  exists S : {set G}, [/\ T = mcut S, T != set0 & odd #|T|].

End EdgeSets.

(** [J] is a [T]-join: the set of the vertices with odd degree in [J] is [T]. *)
Definition is_tjoin (G : mgraph) (T : {set G}) (J : {set edge G}) : Prop :=
  forall v : G, odd (mdeg_in J v) = (v \in T).

(** ** Cycle covers and decompositions

    Families of sets of edges are lists (repetitions are allowed). *)

Section Decompositions.
Variable G : mgraph.
Implicit Types (C F H : {set edge G}) (D L : seq {set edge G}).

(** Each edge is in exactly one member of [D]. *)
Definition medge_partition D : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = 1.

(** [L] is a faithful cycle cover for the weights [p]: each edge [e] is in exactly [p e] cycles
    of [L]. *)
Definition faithful_cycle_cover (p : edge G -> nat) L : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** [D] is a decomposition of [H] into cycles: each edge of [H] is in exactly one cycle of [D], and
    the other edges are in none. *)
Definition cycle_decomposition_of H D : Prop := faithful_cycle_cover (fun e => e \in H) D.

(** [D] is a decomposition of [G] into cycles. *)
Definition cycle_decomposition D : Prop := faithful_cycle_cover (fun=> 1) D.

(** [D] is a decomposition of [G] into paths. *)
Definition mpath_decomposition D : Prop :=
  (forall P, P \in D -> path_subgraph P) /\ medge_partition D.

(** [L] is a cycle double cover: each edge is in exactly two cycles of [L]. *)
Definition cycle_double_cover L : Prop := faithful_cycle_cover (fun=> 2) L.

(** The weights [p] are admissible: each cut has an even total weight, and each of its edges has
    at most half of this weight. *)
Definition admissible_weights (p : edge G -> nat) : Prop :=
  forall (S : {set G}) (e : edge G), e \in mcut S ->
    (2 * p e <= \sum_(f in mcut S) p f)%N /\ ~~ odd (\sum_(f in mcut S) p f).

(** A transition system: a partition of the edges around each vertex into pairs. *)
Definition transition_system (P : G -> {set {set edge G}}) : Prop :=
  (forall v : G, partition (P v) (edges_at v)) /\
  (forall (v : G) (T : {set edge G}), T \in P v -> #|T| = 2).

(** [D] is a cycle decomposition compatible with the transition system [P]: the two edges of a
    cycle around a vertex are not a pair of [P]. *)
Definition compatible_decomposition (P : G -> {set {set edge G}}) D : Prop :=
  cycle_decomposition D /\
  (forall C, C \in D -> forall v : G, (edges_at v :&: C) \notin P v).

End Decompositions.

(** The oddness of [G] (minimum number of odd cycles of a 2-factor) is at most [k]. *)
Definition oddness_le (G : mgraph) (k : nat) : Prop :=
  exists (F : {set edge G}) (D : seq {set edge G}),
    [/\ two_factor F, cycle_decomposition_of F D
      & (count (fun C : {set edge G} => odd #|C|) D <= k)%N].

(** ** Orientations of multigraphs

    An orientation is a map [o : edge G -> bool], which tells if [e] keeps its reference
    direction. *)

(** The tail of [e]. *)
Definition orient_tail (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then source e else target e.

(** The head of [e]. *)
Definition orient_head (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then target e else source e.

(** The in-degree minus the out-degree of [v]. *)
Definition orient_imbalance (G : mgraph) (o : edge G -> bool) (v : G) : int :=
  ((#|[set e | orient_head o e == v]|)%:R - (#|[set e | orient_tail o e == v]|)%:R)%R.

(** [o] is a balanced orientation of [C]: in-degrees and out-degrees are equal. *)
Definition balanced_orientation (G : mgraph) (C : {set edge G}) (o : edge G -> bool) : Prop :=
  forall v : G,
    #|[set e in C | orient_tail o e == v]| = #|[set e in C | orient_head o e == v]|.

(** [G] has an orientable [k]-cycle double cover: [k] even subgraphs with balanced orientations,
    such that each edge is in exactly two of them, with opposite directions. *)
Definition orientable_cycle_cover (G : mgraph) (k : nat) : Prop :=
  exists (C : 'I_k -> {set edge G}) (d : 'I_k -> edge G -> bool),
    [/\ (forall i : 'I_k, even_subgraph (C i)),
        (forall i : 'I_k, balanced_orientation (C i) (d i)),
        (forall e : edge G, #|[set i : 'I_k | e \in C i]| = 2)
      & (forall (e : edge G) (i j : 'I_k),
           i != j -> e \in C i -> e \in C j -> d i e != d j e)].

(** ** Flows

    The values are given in the reference direction of the edges: a negative value is a flow in
    the opposite direction. *)

Section Flows.
Variable G : mgraph.
Local Open Scope ring_scope.

(** [phi], with values in an abelian group, satisfies Kirchhoff's law: the values leaving each
    vertex and the values entering it have the same sum. *)
Definition conservative (V : zmodType) (phi : edge G -> V) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

(** The absolute values of [phi] are between 1 and [k - 1]. *)
Definition nowhere_zero_bounded (k : nat) (phi : edge G -> int) : Prop :=
  forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R.

(** [G] has a nowhere-zero [k]-flow. *)
Definition nowhere_zero_flow (k : nat) : Prop :=
  exists phi : edge G -> int, conservative phi /\ nowhere_zero_bounded k phi.

(** [phi] is a [k]-flow (possibly with zeros). *)
Definition kflow (k : nat) (phi : edge G -> int) : Prop :=
  conservative phi /\ forall e : edge G, `|phi e| <= (k.-1)%:R.

(** [G] has a circular nowhere-zero [r]-flow: a rational flow whose absolute values are between
    1 and [r - 1]. *)
Definition circular_flow (r : rat) : Prop :=
  exists phi : edge G -> rat,
    conservative phi /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= r - 1)%R).

(** The circular flow number of [G] (the infimum of the [r] such that [G] has a circular
    [r]-flow) is at most [c]. *)
Definition circular_flow_number_le (c : rat) : Prop :=
  forall r : rat, (c < r)%R -> circular_flow r.

End Flows.

(** ** Bidirected graphs *)

Section Bidirected.
Local Open Scope ring_scope.

Variable G : mgraph.
Variables ss st : edge G -> int.

(** A bidirection of [G]: signs at the ends of the edges, [ss e] at [source e] and [st e] at
    [target e]. *)
Definition bidirection : Prop :=
  forall e : edge G, ss e \is a GRing.unit /\ st e \is a GRing.unit.

(** The signed sum of the values around [v]. *)
Definition bidirected_net (phi : edge G -> int) (v : G) : int :=
  \sum_(e | source e == v) ss e * phi e + \sum_(e | target e == v) st e * phi e.

(** The bidirected graph has a nowhere-zero [k]-flow. *)
Definition nowhere_zero_biflow (k : nat) : Prop :=
  exists phi : edge G -> int,
    (forall v : G, bidirected_net phi v = 0) /\ nowhere_zero_bounded k phi.

End Bidirected.

(** ** Flow polynomial *)

Section FlowPolynomial.
Variable G : mgraph.
Local Open Scope ring_scope.

(** The number of components of the spanning subgraph with edge set [S]. *)
Definition component_count (S : {set edge G}) : nat :=
  #|components [set: skeleton.skeleton (remove_edges (~: S))]|.

(** The cyclomatic number of the spanning subgraph with edge set [S]. *)
Definition cyclomatic_number (S : {set edge G}) : nat :=
  (#|S| + component_count S - #|G|)%N.

(** The flow polynomial of [G]. *)
Definition flow_poly : {poly int} :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) *: 'X^(cyclomatic_number S).

End FlowPolynomial.

(** ** Simple graphs: cycle space *)

(** [C] is in the cycle space of [G]: a set of edges with even degrees. *)
Definition in_cycle_space (G : sgraph) (C : {set {set G}}) : Prop :=
  C \subset E(G) /\
  (forall v : G, ~~ odd (incidence_degree C v)).

(** [f] is a cycle-continuous map: it maps the edges of [G] to edges of [H], and the preimages of
    the elements of the cycle space are in the cycle space. *)
Definition cycle_continuous (G H : sgraph) (f : {set G} -> {set H}) : Prop :=
  (forall e : {set G}, e \in E(G) -> f e \in E(H)) /\
  (forall C : {set {set H}}, in_cycle_space C ->
     in_cycle_space [set e in E(G) | f e \in C]).

(** ** Simple graphs: cycles and chords *)

(** [G] is cyclically [k]-edge-connected: each cut with cycles on both sides has at least [k]
    edges. *)
Definition cyclically_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    ~ is_forest S -> ~ is_forest (~: S) -> k <= #|cut_edges S|.

(** The number of chords of the cycle [c]. *)
Definition cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & [set p.1; p.2] \notin seq_cycle_edge_list c]]|.

(** ** Linear arboricity *)

(** The edges of [G] can be partitioned into [q] linear forests ([0 < q] is meant). *)
Definition linear_arboricity_le (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q, forall i : 'I_q, linear_forest (edge_color_class col (pred1 i)).

(** The linear arboricity of [G] is [q]. *)
Definition linear_arboricity (G : sgraph) (q : nat) : Prop :=
  linear_arboricity_le G q /\
  forall q' : nat, linear_arboricity_le G q' -> q <= q'.
