(** * General notions on graphs

Simple graphs are those of GraphTheory ([sgraph], edge relation [--]), and multigraphs are
its labelled multigraphs [graph Lv Le] with trivial labels: each edge [e] has two ends
[source e] and [target e], whose order is irrelevant here; loops and parallel edges are
allowed.  Walks, paths and cycles of simple graphs are sequences of vertices. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph coloring connectivity.
From GraphTheory Require dom skeleton.
From mathcomp Require Import boot order algebra fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic and asymptotics *)

(** The ceiling of [a / b] (0 if [b = 0]). *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

Lemma sqrt_ceil_ex (n : nat) : exists s : nat, n <= s ^ 2.
Proof. by exists n; rewrite expnS expn1; case: n => // m; rewrite leq_pmulr. Qed.

(** The ceiling of the square root of [n]: the least [s] such that [n <= s ^ 2]. *)
Definition sqrt_ceil (n : nat) : nat := ex_minn (sqrt_ceil_ex n).

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f] tends to infinity. *)
Definition tends_to_infinity (f : nat -> nat) : Prop :=
  forall b : nat, eventually (fun n => b <= f n).

(** [f = O(g)]. *)
Definition big_O_nat (f g : nat -> nat) : Prop :=
  exists C : nat, 0 < C /\ eventually (fun n => f n <= C * g n).

(** [f = Theta(g)]. *)
Definition big_Theta_nat (f g : nat -> nat) : Prop :=
  big_O_nat f g /\ big_O_nat g f.

(** ** Graphs given by a relation or a set of edges *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** The relation given by a set of pairs. *)
Definition edge_set_rel (V : finType) (E : {set {set V}}) : rel V :=
  fun x y => [set x; y] \in E.

(** The graph on [V] with edge set [E]. *)
Definition sgraph_of_edges (V : finType) (E : {set {set V}}) : sgraph :=
  sgraph_of_rel (edge_set_rel E).

(** The graph on [0, ..., n-1] whose edges are listed in [es]. *)
Definition edge_list_graph (n : nat) (es : seq (nat * nat)) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i, val j) \in es).

(** [T] is the edge set of a spanning tree of [G]. *)
Definition spanning_tree (G : sgraph) (T : {set {set G}}) : bool :=
  [&& T \subset E(G), is_forestb [set: sgraph_of_edges T]
    & connectedb [set: sgraph_of_edges T]].

(** ** Degrees *)

(** The maximum degree of [G] (0 if [G] is empty). *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** The degrees of the vertices of [G]. *)
Definition degree_sequence (G : sgraph) : seq nat := [seq #|N(v)| | v : G].

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** Every vertex has degree at least [d] (true if [G] is empty). *)
Definition min_degree_ge (G : sgraph) (d : nat) : Prop := forall v : G, d <= #|N(v)|.

(** The minimum degree of [G] is [d] (false if [G] is empty). *)
Definition min_degree (G : sgraph) (d : nat) : Prop :=
  min_degree_ge G d /\ exists v : G, #|N(v)| = d.

(** Every vertex has degree at most 3. *)
Definition subcubic (G : sgraph) : Prop := forall v : G, #|N(v)| <= 3.

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** The subgraph induced by [W] is [k]-degenerate: each nonempty subset [S] of [W] has a
    vertex with at most [k] neighbours in [S]. *)
Definition degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G}, S \subset W -> S != set0 -> exists x, (x \in S) /\ #|N(x) :&: S| <= k.
Arguments degenerate_on {G} W k.

(** [G] is [k]-degenerate. *)
Definition degenerate (G : sgraph) (k : nat) : Prop :=
  degenerate_on [set: G] k.

(** [G] is strongly regular with parameters [k], [lam] and [mu] (complete and edgeless graphs
    are not excluded). *)
Definition strongly_regular (G : sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_neigh x y| = lam)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_neigh x y| = mu)].

(** ** Sets of vertices *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

(** Every vertex of [A] is adjacent to every vertex of [B]. *)
Definition complete_between (G : sgraph) (A B : {set G}) : bool :=
  [forall a in A, [forall b in B, a -- b]].

(** The number of pairs [(a, b)] of adjacent vertices with [a] in [A] and [b] in [B] (an edge
    with both ends in both sets is counted twice). *)
Definition edge_count_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

(** The vertices outside [U] with a neighbour in [U]. *)
Definition external_neigh (G : sgraph) (U : {set G}) : {set G} := NS(U) :\: U.

(** [T] is a triangle: a clique on three vertices. *)
Definition triangle (G : sgraph) (T : {set G}) : Prop := clique T /\ #|T| = 3.

(** The number of nonempty cliques of [G]. *)
Definition nonempty_clique_count (G : sgraph) : nat :=
  #|[set S in cliques [set: G] | S != set0]|.

(** The number of cliques of [G] on [r] vertices. *)
Definition clique_count_size (G : sgraph) (r : nat) : nat :=
  #|[set S in cliques [set: G] | #|S| == r]|.

(** ** Walks, paths and cycles as sequences *)

Section Sequences.
Variable T : finType.
Implicit Types (s c : seq T) (x y : T).

(** The elements of [s] other than [x] and [y]. *)
Definition seq_interior x y s : {set T} := [set:: s] :\: [set x; y].

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

(** The set of the pairs of consecutive elements of [s]: the edge set of a walk. *)
Definition seq_edge_set s : {set {set T}} := [set e in seq_edge_list s].

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

(** The set of the pairs of consecutive elements of the cyclic sequence [c]: the edge set of the
    cycle [c]. *)
Definition seq_cycle_edge_set c : {set {set T}} := [set e in seq_cycle_edge_list c].

End Sequences.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c d : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

(** [c] is a longest cycle of [r]. *)
Definition seq_longest_cycle c : Prop :=
  seq_cycle c /\ forall d, seq_cycle d -> size d <= size c.

End Cycles.

Section Paths.
Variable G : diGraph.
Implicit Types (p : seq G) (X Y : {set G}).

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

(** [p] is a longest path. *)
Definition seq_longest_path p : Prop :=
  seq_simple_path p /\ forall q : seq G, seq_simple_path q -> size q <= size p.

(** [p] is a path from a vertex of [X] to a vertex of [Y]. *)
Definition seq_path_between X Y p : bool :=
  if p is x :: q then [&& x \in X, last x q \in Y & seq_simple_path p] else false.

End Paths.

Section InducedPathsCycles.
Variable G : sgraph.
Implicit Types (c p : seq G) (a b u v : G).

(** [p] is an induced path (possibly empty): adjacent vertices of [p] are consecutive. *)
Definition chordless_path p : Prop :=
  [/\ uniq p, sorted (--) p
    & forall u v : G, u \in p -> v \in p -> u -- v -> [set u; v] \in seq_edge_list p].

(** [p] is an induced path from [a] to [b]. *)
Definition chordless_path_between a b p : Prop :=
  [/\ chordless_path p, ohead p = Some a & last a p = b].

(** Adjacent vertices of [c] are consecutive in the cyclic sequence [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> [set u; v] \in seq_cycle_edge_list c.

(** [c] is an induced cycle (of length at least 3). *)
Definition chordless_cycle c : Prop := seq_cycle (--) c /\ cyclic_chordless c.

(** [c] is a hole: an induced cycle of length at least 4. *)
Definition hole c : Prop := chordless_cycle c /\ 3 < size c.

(** [G] has a hole of length [L]. *)
Definition has_hole_of_length (L : nat) : Prop := exists c, hole c /\ size c = L.

(** [G] has holes of [l] consecutive lengths. *)
Definition consecutive_holes (l : nat) : Prop :=
  exists t : nat, forall i : nat, 1 <= i -> i <= l -> has_hole_of_length (t + i).

(** [G] has no hole of even length. *)
Definition even_hole_free : Prop :=
  forall c : seq G,
    hole c ->
    ~~ odd (size c) ->
    False.

End InducedPathsCycles.
Arguments cyclic_chordless {G} c.
Arguments hole {G} c.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** The girth of [G] is [g]. *)
Definition girth (G : sgraph) (g : nat) : Prop :=
  girth_ge G g /\ (exists c : seq G, seq_cycle (--) c /\ size c = g).

(** [G] has no cycle whose length is between [lo] and [hi]. *)
Definition no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> lo <= size c -> size c <= hi -> False.

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** ** Distances *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

(** The [m]-th power of [G]: distinct vertices at distance at most [m] are adjacent. *)
Definition graph_power (G : sgraph) (m : nat) : sgraph :=
  sgraph_of_rel (fun x y : G => y \in ball m x).

(** The vertices at distance at most [r] from [S]. *)
Definition set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) ball r x.

(** Distinct sequences of the list [paths] are at distance at least [d] ([0 < d] is meant). *)
Definition pairwise_distant_seqs (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G, p \in paths -> q \in paths -> p != q ->
    [disjoint set_ball d.-1 [set:: p] & [set:: q]].

(** There are [k] paths from [X] to [Y] pairwise at distance at least [d]. *)
Definition has_distant_paths (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> seq_path_between X Y p) /\
    pairwise_distant_seqs d paths.

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

(** [v] is on a shortest path from [u] to [w] ([G] is connected). *)
Definition metric_between (G : sgraph) (u v w : G) : bool :=
  graph_dist u v + graph_dist v w == graph_dist u w.

(** The line through [a] and [b] in the metric space of [G] (Chen and Chvatal): the vertices
    [x] such that one of [a], [b], [x] is between the two others. *)
Definition metric_line (G : sgraph) (a b : G) : {set G} :=
  [set x : G |
      metric_between a b x || metric_between a x b || metric_between x a b].

(** The number of lines of [G]. *)
Definition metric_line_count (G : sgraph) : nat :=
  #|[set L : {set G} |
      [exists a : G, [exists b : G, (a != b) && (L == metric_line a b)]]]|.

(** ** Subgraphs *)

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** [G] has no induced subgraph isomorphic to [H]. *)
Definition induced_free (G H : sgraph) : Prop := ~ has_induced_copy G H.

(** A class of graphs is closed under isomorphism. *)
Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

(** A class of graphs is closed under taking induced subgraphs on subsets of vertices. *)
Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

(** A class of graphs is hereditary. *)
Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

(** [A] is the edge set of a copy of [T] in [G] (as a subgraph). *)
Definition embedded_edge_copy (G T : sgraph) (A : {set {set G}}) : Prop :=
  exists f : T -> G,
    [/\ injective f,
        (forall x y : T, x -- y -> f x -- f y)
      & A = [set f @: (e : {set T}) | e in E(T)]].
Arguments embedded_edge_copy {G} T A.

(** The edges of [G] are partitioned by the copies of [T] whose edge sets are listed in [D]. *)
Definition edge_decomposition (G T : sgraph) (D : seq {set {set G}}) : Prop :=
  (forall A, A \in D -> embedded_edge_copy T A) /\
  (forall e : {set G},
     count (fun A : {set {set G}} => e \in A) D = ((e \in E(G)) : nat)).
Arguments edge_decomposition {G} T D.

Section DelEdgeSet.
Variables (G : sgraph) (F : {set {set G}}).

(** The edges of [G] that are not in [F]. *)
Definition del_edge_set_rel : rel G := [rel x y : G | (x -- y) && ([set x; y] \notin F)].

Lemma del_edge_set_sym : symmetric del_edge_set_rel.
Proof. by move=> x y; rewrite /del_edge_set_rel /= sg_sym setUC. Qed.

Lemma del_edge_set_irrefl : irreflexive del_edge_set_rel.
Proof. by move=> x; rewrite /del_edge_set_rel /= sg_irrefl. Qed.

(** [G] without the edges of [F]. *)
Definition del_edge_set : sgraph := SGraph del_edge_set_sym del_edge_set_irrefl.

End DelEdgeSet.

(** ** Connectivity, edge-connectivity, bridges *)

(** The edges with exactly one end in [S]. *)
Definition cut_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in E(G) | (e :&: S != set0) && (e :&: (~: S) != set0)].

(** [G] is [k]-edge-connected: every cut has at least [k] edges (always true if [G] has at most
    one vertex). *)
Definition edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|cut_edges S|.

(** The local connectivity of any two distinct vertices is at most [k]: every set of internally
    disjoint paths between them has at most [k] elements. *)
Definition local_connectivity_le (G : sgraph) (k : nat) : Prop :=
  forall (x y : G) (P : {set IPath x y}),
    x != y ->
    (forall p q : IPath x y, p \in P -> q \in P -> p != q -> independent p q) ->
    #|P| <= k.

(** [e] is a bridge: an edge whose ends are in different components when it is deleted. *)
Definition bridge (G : sgraph) (e : {set G}) : bool :=
  (e \in E(G)) &&
  [exists x in e, exists y in e, ~~ connect (del_edges_rel e) x y].

(** The number of bridges of [G]. *)
Definition bridge_count (G : sgraph) : nat :=
  #|[set e : {set G} | bridge e]|.

(** ** Classes of graphs *)

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** [G] is a disjoint union of paths. *)
Definition linear_forest (G : sgraph) : Prop := is_forest [set: G] /\ Delta G <= 2.

(** ** Usual graphs *)

(** The path on [n] vertices. *)
Definition path_graph (n : nat) : sgraph := sgraph_of_rel (fun i j : 'I_n => (val i).+1 == val j).

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** The wheel with [l] spokes: a cycle of length [l] and a vertex adjacent to all its vertices
    ([3 <= l] is meant). *)
Definition wheel (l : nat) : sgraph := add_node (cycle_graph l) [set: cycle_graph l].

Section CompleteMultipartite.
Variables k m : nat.

(** Vertices in different parts. *)
Definition complete_multipartite_rel : rel ('I_k * 'I_m) := fun x y => x.1 != y.1.

Lemma complete_multipartite_sym : symmetric complete_multipartite_rel.
Proof. by move=> x y; rewrite /complete_multipartite_rel eq_sym. Qed.

Lemma complete_multipartite_irrefl : irreflexive complete_multipartite_rel.
Proof. by move=> x; rewrite /complete_multipartite_rel eqxx. Qed.

(** The complete multipartite graph with [k] parts of size [m]. *)
Definition complete_multipartite : sgraph :=
  SGraph complete_multipartite_sym complete_multipartite_irrefl.

End CompleteMultipartite.

Section Hypercube.
Variable d : nat.

(** Tuples that differ at exactly one position. *)
Definition hypercube_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.

Lemma hypercube_sym : symmetric hypercube_rel.
Proof.
move=> x y; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth y i] = [set i : 'I_d | tnth y i != tnth x i] by [].
by apply/setP => i; rewrite !inE eq_sym.
Qed.

Lemma hypercube_irrefl : irreflexive hypercube_rel.
Proof.
move=> x; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth x i] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE eqxx.
Qed.

(** The hypercube of dimension [d]. *)
Definition hypercube : sgraph := SGraph hypercube_sym hypercube_irrefl.

End Hypercube.

(** The Petersen graph: the edges are those of the outer 5-cycle, the spokes and those of the
    inner pentagram. *)
Definition petersen_graph : sgraph :=
  edge_list_graph 10
    [:: (0,1); (1,2); (2,3); (3,4); (4,0);
        (0,5); (1,6); (2,7); (3,8); (4,9);
        (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.

(** The diamond: [K_4] minus an edge. *)
Definition diamond : sgraph := del_edges ([set ord0; ord_max] : {set 'K_4}).

(** The (undirected) Cayley graph of the group [gT] for the connection set [S] (made symmetric,
    without the neutral element). *)
Definition cayley_graph (gT : finGroupType) (S : {set gT}) : sgraph :=
  sgraph_of_rel (fun x y : gT => (x^-1 * y)%g \in S).

(** ** Operations on graphs *)

Section GraphJoin.
Variables G H : sgraph.

(** The edges of [G], those of [H], and all pairs of a vertex of [G] and a vertex of [H]. *)
Definition graph_join_rel : rel (G + H)%type := fun u v =>
  match u, v with
  | inl x, inl y => x -- y
  | inr x, inr y => x -- y
  | _, _ => true
  end.

Lemma graph_join_sym : symmetric graph_join_rel.
Proof. by move=> [x|x] [y|y] //=; rewrite sgP. Qed.

Lemma graph_join_irrefl : irreflexive graph_join_rel.
Proof. by move=> [x|x] /=; rewrite sgP. Qed.

(** The join of [G] and [H]. *)
Definition graph_join : sgraph := SGraph graph_join_sym graph_join_irrefl.

End GraphJoin.

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

(** Adjacent in both coordinates. *)
Definition tensor_rel : rel (G * H) :=
  fun p q => (p.1 -- q.1) && (p.2 -- q.2).

Lemma tensor_sym : symmetric tensor_rel.
Proof. by move=> p q; rewrite /tensor_rel ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'. Qed.

Lemma tensor_irrefl : irreflexive tensor_rel.
Proof. by move=> p; rewrite /tensor_rel !sg_irrefl. Qed.

(** The tensor (direct, categorical) product of [G] and [H]. *)
Definition tensor_product : sgraph := SGraph tensor_sym tensor_irrefl.

(** Equal or adjacent in each coordinate, and distinct. *)
Definition strong_rel : rel (G * H) :=
  fun p q => box_rel p q || tensor_rel p q.

Lemma strong_sym : symmetric strong_rel.
Proof. by move=> p q; rewrite /strong_rel box_sym tensor_sym. Qed.

Lemma strong_irrefl : irreflexive strong_rel.
Proof. by move=> p; rewrite /strong_rel box_irrefl tensor_irrefl. Qed.

(** The strong product of [G] and [H]. *)
Definition strong_product : sgraph := SGraph strong_sym strong_irrefl.

End Products.

Section Subdivision.
Variables (G : sgraph) (n : nat).

(** The edges, with a fixed orientation. *)
Definition oriented_edge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

Local Abbreviation EdgeT := {p : G * G | oriented_edge p}.

(** The vertices of the subdivision: those of [G], and [n-1] vertices for each edge. *)
Definition subdivision_vertex : Type := (G + (EdgeT * 'I_n.-1))%type.

(** The edges of the subdivision, in one direction. *)
Definition subdivision_rel (x y : subdivision_vertex) : bool :=
  match x, y with
  | inl _, inl _ => false
  | inl a, inr (e, i) =>
      ((a == (val e).1) && (val i == 0)) || ((a == (val e).2) && (val i == n.-1.-1))
  | inr _, inl _ => false
  | inr (e, i), inr (e', j) => (e == e') && ((val i).+1 == val j)
  end.

(** [G] with each edge replaced by a path of length [n] ([2 <= n] is meant). *)
Definition subdivision : sgraph := sgraph_of_rel subdivision_rel.

End Subdivision.

(** The fractional power [G^(m/n)]: the [m]-th power of the [n]-subdivision of [G]
    ([2 <= n] is meant). *)
Definition fractional_power (G : sgraph) (m n : nat) : sgraph := graph_power (subdivision G n) m.

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

(** ** Multigraphs *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** The maximum number of edges incident to a vertex (a loop is counted once). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Every vertex is incident to three edges (a loop is counted once). *)
Definition mcubic (G : mgraph) : Prop := mregular G 3.

(** [G] is cubic and has no loop. *)
Definition loopless_cubic (G : mgraph) : Prop := mloopless G /\ mcubic G.

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

Lemma mline_rel_sym (G : mgraph) : symmetric (@mline_rel G).
Proof.
move=> e1 e2; rewrite /mline_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.

Lemma mline_rel_irrefl (G : mgraph) : irreflexive (@mline_rel G).
Proof. by move=> e; rewrite /mline_rel eqxx. Qed.

(** The line graph of the multigraph [G] (parallel edges are adjacent). *)
Definition mline_graph (G : mgraph) : sgraph := SGraph (@mline_rel_sym G) (@mline_rel_irrefl G).

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** The degree of [v] (a loop is counted twice). *)
Definition mdeg (G : mgraph) (v : G) : nat := mdeg_in [set: edge G] v.

(** [H] is the edge set of a [k]-regular subgraph. *)
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, mdeg_in H v = 0 \/ mdeg_in H v = k.

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** [w] is a walk from [x] to [y] with edges in [H]. *)
Definition uwalk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  uwalk x y w && all (fun e => e \in H) w.

(** There are [k] edge-disjoint walks from [x] to [y], or, equivalently, [k] edge-disjoint paths
    ([x] and [y] are meant to be distinct). *)
Definition medge_disjoint_paths (G : mgraph) (x y : G) (k : nat) : Prop :=
  exists ws : seq (seq (edge G)),
    [/\ size ws = k,
        (forall w : seq (edge G), w \in ws -> uwalk x y w)
      & (forall e : edge G, count (fun w : seq (edge G) => e \in w) ws <= 1)].

(** [G] is [k]-edge-connected: it remains connected when fewer than [k] edges are deleted. *)
Definition medge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, #|E| < k -> connected [set: skeleton.skeleton (remove_edges E)].

(** The vertex [x] is an end of an edge of [H]. *)
Definition subgraph_incident (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

(** The subgraph with edge set [H] and without isolated vertices is connected. *)
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, subgraph_incident H x -> subgraph_incident H y -> exists w, uwalk_in H x y w.

(** [C] is the edge set of a cycle of [G] (a loop and a pair of parallel edges are cycles). *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** [e] is a bridge: every walk between its ends uses it. *)
Definition mbridge (G : mgraph) (e : edge G) : Prop :=
  forall w : seq (edge G), uwalk (source e) (target e) w -> e \in w.

(** [G] has no bridge. *)
Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ mbridge e.

(** [G] and [H] are isomorphic: there are bijections between their vertices and between their
    edges that preserve the incidence. *)
Definition misomorphic (G H : mgraph) : Prop :=
  exists (f : G -> H) (g : edge G -> edge H),
    [/\ bijective f, bijective g & forall x e, incident (f x) (g e) = incident x e].

(** [G] where the edge [e0] from [x] to [y] is replaced by a path [x z y], for a new vertex [z],
    which is [None]: [e0] becomes the edge [x z], and [None] is the new edge [z y]. *)
Definition msubdivide_edge (G : mgraph) (e0 : edge G) : mgraph :=
  @Graph unit unit (option G) (option (edge G))
    (fun b oe =>
       match oe with
       | Some e => if b && (e == e0) then None else Some (endpoint b e)
       | None => if b then Some (target e0) else None
       end)
    (fun=> tt) (fun=> tt).

(** [K] is a subdivision of [G], up to isomorphism: it is obtained by subdividing edges one by
    one. *)
Inductive msubdivision (G K : mgraph) : Prop :=
| msubdivision_iso of misomorphic G K
| msubdivision_step (e : edge G) of msubdivision (msubdivide_edge e) K.

(** [G] and [H] are homeomorphic: they have a common subdivision. *)
Definition mhomeomorphic (G H : mgraph) : Prop :=
  exists K : mgraph, msubdivision G K /\ msubdivision H K.

(** ** Finite probability and random graphs *)

(** [P n] holds with high probability: its probability tends to 1.  The probabilities of the
    elements of the finite type [T n] are the integers [w n x], divided by their sum. *)
Definition whp
    (T : nat -> finType) (w : forall n : nat, T n -> nat)
    (P : forall n : nat, pred (T n)) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      0 < \sum_x w n x /\
      b * (\sum_(x | P n x) w n x) >= (b - a) * (\sum_x w n x)).

(** The probability that the edge set of the random graph [G(n,p)] on [0, ..., n-1] satisfies
    [P]. *)
Definition gnp_probability (R : realFieldType) (p : R) (n : nat) (P : pred {set {set 'I_n}}) : R :=
  (\sum_(E : {set {set 'I_n}} | (E \subset E('K_n)) && P E)
    p ^+ #|E| * (1 - p) ^+ (#|E('K_n)| - #|E|))%R.

(** The edge set of the random graph [G(n,p)] satisfies [P n] with high probability. *)
Definition gnp_whp (R : realFieldType) (p : R) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  forall eps : R, (0 < eps)%R -> eventually (fun n => (1 - eps <= gnp_probability p (P n))%R).

(** ** Polynomial-time algorithms

    Algorithms are programs of a small language over first-order data (unary natural numbers,
    pairs and lists), whose interpreter computes both the result and a number of steps.  The
    language contains the primitive recursive functions, and the functions it computes in
    polynomial time are those of P. *)

(** Data. *)
Inductive data : Type :=
| Dnat  of nat
| Dpair of data & data
| Dnil
| Dcons of data & data.

(** The size of [d] (numbers are in unary). *)
Fixpoint data_size (d : data) : nat :=
  match d with
  | Dnat n => n.+1
  | Dpair a b => (data_size a + data_size b).+1
  | Dnil => 1
  | Dcons a b => (data_size a + data_size b).+1
  end.

(** Equality of data. *)
Fixpoint data_eq (a b : data) : bool :=
  match a, b with
  | Dnat m, Dnat n => m == n
  | Dpair x y, Dpair u v => data_eq x u && data_eq y v
  | Dnil, Dnil => true
  | Dcons x y, Dcons u v => data_eq x u && data_eq y v
  | _, _ => false
  end.

(** Programs: identity, constants, composition, pairs, lists, equality test, arithmetic,
    iteration and recursion on lists. *)
Inductive prog : Type :=
| Pid | Pconst of data
| Pcomp of prog & prog          (* left, then right *)
| Ppair of prog & prog | Pfst | Psnd
| Pcons of prog & prog
| Pcase of prog & prog         (* right on (Dpair a b) if the input is Dcons a b, else left *)
| Peq                           (* Dpair a b => Dnat (data_eq a b) *)
| Padd | Pmul | Ppred
| Pnatrec of prog               (* Dpair (Dnat n) seed => iterate the body n times on seed *)
| Pfold of prog & prog.         (* recursion on lists: nil case, cons case *)

(** The result of a program and its number of steps. *)
Fixpoint prog_eval (p : prog) (d : data) : data * nat :=
  match p with
  | Pid => (d, 1)
  | Pconst k => (k, 1)
  | Pcomp p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 r1.1 in
      (r2.1, (r1.2 + r2.2).+1)
  | Ppair p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 d in
      (Dpair r1.1 r2.1, (r1.2 + r2.2).+1)
  | Pfst => (if d is Dpair a _ then a else d, 1)
  | Psnd => (if d is Dpair _ b then b else d, 1)
  | Pcons p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 d in
      (Dcons r1.1 r2.1, (r1.2 + r2.2).+1)
  | Pcase p1 p2 =>
      match d with
      | Dcons a b => let r := prog_eval p2 (Dpair a b) in (r.1, r.2.+1)
      | _ => let r := prog_eval p1 d in (r.1, r.2.+1)
      end
  | Peq => (if d is Dpair a b then Dnat (data_eq a b) else Dnat 0, data_size d)
  | Padd => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a + b) else Dnat 0, data_size d)
  | Pmul => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a * b) else Dnat 0, data_size d)
  | Ppred => (if d is Dnat n then Dnat n.-1 else Dnat 0, 1)
  | Pnatrec body =>
      match d with
      | Dpair (Dnat n) seed =>
          (fix N (n : nat) (acc : data) (c : nat) : data * nat :=
             match n with
             | 0 => (acc, c.+1)
             | m.+1 => N m (prog_eval body acc).1 (c + (prog_eval body acc).2).+1
             end) n seed 0
      | _ => (d, 1)
      end
  | Pfold pn pc =>
      (fix F (d : data) : data * nat :=
         match d with
         | Dcons a b =>
             (  (prog_eval pc (Dpair a (F b).1)).1,
                ((F b).2 + (prog_eval pc (Dpair a (F b).1)).2).+1 )
         | _ => ((prog_eval pn d).1, (prog_eval pn d).2.+1)
         end) d
  end.

(** The result of [p] on [d]. *)
Definition prog_run  (p : prog) (d : data) : data := (prog_eval p d).1.

(** The number of steps of [p] on [d]. *)
Definition prog_cost (p : prog) (d : data) : nat  := (prog_eval p d).2.

(** [p] is polynomial on the encodings of the elements of [T]. *)
Definition polytime_on (T : Type) (enc : T -> data) (p : prog) : Prop :=
  exists c k : nat, forall x : T, prog_cost p (enc x) <= c * (data_size (enc x)) ^ k + c.

(** [p] decides [P]. *)
Definition decides_on (T : Type) (enc : T -> data) (P : T -> Prop) (p : prog) : Prop :=
  forall x : T, prog_run p (enc x) = Dnat 1 <-> P x.

(** Some polynomial program satisfies [Spec] on the elements of [Class]. *)
Definition polytime_outputs (T : Type) (enc : T -> data)
    (Class : T -> Prop) (Spec : T -> data -> Prop) : Prop :=
  exists p : prog, polytime_on enc p /\
    forall x : T, Class x -> Spec x (prog_run p (enc x)).

(** The encoding of a list. *)
Definition enc_list (ds : seq data) : data := foldr Dcons Dnil ds.

(** The encoding of a boolean. *)
Definition enc_bool (b : bool) : data := Dnat b.

(** The natural number encoded by [d] (0 if there is none). *)
Definition data_nat_value (d : data) : nat :=
  if d is Dnat n then n else 0.

(** The encoding of a graph: its adjacency matrix. *)
Definition enc_graph (G : sgraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum G] | i <- enum G].

(** ** Families of sets, Stirling numbers *)

(** The number of members of [F] that contain [v]: the degree of [v] in the hypergraph [F], or
    in the spanning subgraph with edge set [F]. *)
Definition incidence_degree (T : finType) (F : {set {set T}}) (v : T) : nat :=
  #|[set e in F | v \in e]|.

(** The number of vertices of degree [k] in the spanning subgraph of [G] with edge set [F]. *)
Definition degree_class_size (G : sgraph) (F : {set {set G}}) (k : nat) : nat :=
  #|[set v : G | incidence_degree F v == k]|.

(** The Stirling numbers of the second kind: the number of partitions of a set with [k] elements
    into [r] parts. *)
Fixpoint stirling2 (k r : nat) : nat :=
  match k, r with
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _.+1, 0 => 0
  | k'.+1, r'.+1 => r'.+1 * stirling2 k' r'.+1 + stirling2 k' r'
  end.

(** ** Finite posets

    Orders are boolean relations. *)

(** [le] is an order. *)
Definition is_order (X : finType) (le : rel X) : Prop :=
  [/\ reflexive le, antisymmetric le & transitive le].

(** [l] is a linear order. *)
Definition is_linear_order (X : finType) (l : rel X) : Prop :=
  [/\ reflexive l, antisymmetric l, transitive l & total l].

(** The list [ls] is a realizer of [le]: linear extensions whose intersection is [le]. *)
Definition realizer (X : finType) (le : rel X) (ls : seq (rel X)) : Prop :=
  (forall i : nat, i < size ls ->
     is_linear_order (nth (fun _ _ => false) ls i) /\
     subrel le (nth (fun _ _ => false) ls i)) /\
  (forall x y : X, le x y <->
     (forall i : nat, i < size ls -> (nth (fun _ _ => false) ls i) x y)).

(** The (Dushnik-Miller) dimension of the order [le] is at most [d]. *)
Definition poset_dim_le (X : finType) (le : rel X) (d : nat) : Prop :=
  exists ls : seq (rel X), size ls <= d /\ realizer le ls.

(** The height (maximum size of a chain) is at most [h]. *)
Definition poset_height_le (X : finType) (le : rel X) (h : nat) : Prop :=
  forall A : {set X}, {in A &, total le} -> #|A| <= h.

(** [y] covers [x]. *)
Definition poset_cover_rel (X : finType) (le : rel X) (x y : X) : bool :=
  [&& le x y, x != y &
      [forall z : X, (le x z && le z y) ==> ((z == x) || (z == y))]].

(** The cover graph (undirected Hasse diagram) of the order [le]. *)
Definition poset_cover_graph (X : finType) (le : rel X) : sgraph :=
  sgraph_of_rel (poset_cover_rel le).

(** ** More classes of graphs *)

(** [G] has no induced claw ([K_1,3]). *)
Definition claw_free (G : sgraph) : Prop := induced_free G 'K_1,3.

(** [G] is complete multipartite with parts given by some function. *)
Definition is_complete_multipartite (G : sgraph) : Prop :=
  exists (k : nat) (p : G -> 'I_k), forall x y : G, x -- y = (p x != p y).

(** [G] is normal (Koerner): it has a set [K] of cliques and a set [A] of stable sets, both
    covering the vertices, such that each clique of [K] meets each stable set of [A]. *)
Definition normal_graph (G : sgraph) : bool :=
  [exists K : {set {set G}},
    [exists A : {set {set G}},
      [forall C in K, cliqueb C] &&
      [forall S in A, dom.stable S] &&
      [forall v : G, [exists C in K, v \in C]] &&
      [forall v : G, [exists S in A, v \in S]] &&
      [forall C in K, [forall S in A, C :&: S != set0]]]].

(** The adjacency of the triangular lattice, in coordinates. *)
Definition triangular_lattice_adj (a b : nat * nat) : bool :=
  let: (x1, y1) := a in let: (x2, y2) := b in
  [|| ((x2 == x1.+1) && (y2 == y1)),
      ((x1 == x2.+1) && (y1 == y2)),
      ((x1 == x2) && (y2 == y1.+1)),
      ((x1 == x2) && (y1 == y2.+1)),
      ((x2 == x1.+1) && (y1 == y2.+1)) |
      ((x1 == x2.+1) && (y2 == y1.+1))].

(** [G] is hexagonal: an induced subgraph of the triangular lattice. *)
Definition hexagonal (G : sgraph) : Prop :=
  exists phi : G -> nat * nat,
    injective phi /\
    (forall u v : G, u != v -> (u -- v) = triangular_lattice_adj (phi u) (phi v)).

(** The list [s] is graphic: it is, up to order, the list of the degrees of some graph. *)
Definition graphic (s : seq nat) : Prop :=
  exists H : sgraph, perm_eq s (degree_sequence H).

(** ** More on distances *)

(** [G] is connected of diameter [d] ([0 < d] is meant). *)
Definition diameter (G : sgraph) (d : nat) : Prop :=
  (forall u v : G, v \in ball d u) /\ (exists u v : G, v \notin ball d.-1 u).

(** The Wiener index: the sum of the distances between the pairs of vertices ([G] is
    connected). *)
Definition wiener_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G) graph_dist u v) %/ 2.

(** The number of vertices closer to [u] than to [v]. *)
Definition closer_count (G : sgraph) (u v : G) : nat :=
  #|[set x : G | graph_dist x u < graph_dist x v]|.

(** The Szeged index: the sum over the edges [u v] of the number of vertices closer to [u] times
    the number of vertices closer to [v] ([G] is connected). *)
Definition szeged_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G | u -- v) closer_count u v * closer_count v u) %/ 2.

(** ** Blocks *)

(** [B] is nonempty and induces a connected subgraph without cut vertex. *)
Definition no_cut_vertex (G : sgraph) (B : {set G}) : bool :=
  [&& B != set0, connectedb B & [forall v in B, connectedb (B :\ v)]].

(** [B] is a block: a maximal set that induces a connected subgraph without cut vertex. *)
Definition is_block (G : sgraph) (B : {set G}) : bool :=
  no_cut_vertex B &&
  [forall B' : {set G}, (B \subset B') && no_cut_vertex B' ==> (B' == B)].

(** The vertex [v] is in the block [B]. *)
Definition block_tree_rel (G : sgraph) : rel (G + {set G})%type :=
  fun p q => match p, q with
             | inl v, inr B => (v \in B) && is_block B
             | _, _ => false
             end.

(** The bipartite graph between vertices and blocks (a vertex and a block are adjacent if the
    vertex is in the block); the sets of vertices that are not blocks are isolated vertices. *)
Definition block_tree (G : sgraph) : sgraph := sgraph_of_rel (@block_tree_rel G).

(** ** Labellings and layouts *)

(** The edges, with a fixed orientation. *)
Definition oriented_edges (G : sgraph) : {set G * G} :=
  [set p : G * G | oriented_edge p].

(** The difference of the labels of the ends of [p]. *)
Definition edge_label (G : sgraph) (l : G -> nat) (p : G * G) : nat :=
  (l p.1 - l p.2) + (l p.2 - l p.1).

(** [l] is a graceful labelling: distinct labels from 0 to the number [m] of edges, whose
    differences on the edges are distinct and between 1 and [m]. *)
Definition graceful_labeling (G : sgraph) (l : G -> nat) : Prop :=
  [/\ injective l,
      (forall v : G, l v <= #|E(G)|),
      (forall p : G * G, p \in oriented_edges G ->
         (1 <= edge_label l p) && (edge_label l p <= #|E(G)|)) &
      {in oriented_edges G &, injective (edge_label l)}].

(** [G] has a book embedding with [k] pages: an order of its vertices and an assignment of its
    edges to [k] pages without crossing edges on a page. *)
Definition book_embedding (G : sgraph) (k : nat) : Prop :=
  exists (pos : G -> nat) (col : G -> G -> nat),
    [/\ injective pos,
        (forall x y : G, col x y = col y x),
        (forall x y : G, col x y < k) &
        (forall a b c d : G,
           a -- b -> c -- d -> col a b = col c d ->
           ~~ ((pos a < pos c) && (pos c < pos b) && (pos b < pos d)))].

(** The book thickness (page number) of [G] is [k]. *)
Definition book_thickness (G : sgraph) (k : nat) : Prop :=
  book_embedding G k /\ (forall m : nat, book_embedding G m -> k <= m).

(** ** Pebbling *)

(** A pebbling move: two pebbles are removed from a vertex, and one is added to a neighbour. *)
Definition pebble_move (G : sgraph) (D D' : G -> nat) : Prop :=
  exists u v : G,
    [/\ u -- v, 2 <= D u &
        forall w : G, D' w = if w == u then D u - 2
                             else if w == v then D v + 1 else D w].

(** The distribution of pebbles [D'] is reached from [D] by pebbling moves. *)
Inductive pebble_reach (G : sgraph) : (G -> nat) -> (G -> nat) -> Prop :=
| pebble_reach_refl (D : G -> nat) : pebble_reach D D
| pebble_reach_step (D D' D'' : G -> nat) :
    pebble_move D D' -> pebble_reach D' D'' -> pebble_reach D D''.

(** Pebbling moves from [D] can bring a pebble to [r]. *)
Definition pebble_solvable (G : sgraph) (D : G -> nat) (r : G) : Prop :=
  exists D' : G -> nat, pebble_reach D D' /\ 1 <= D' r.

(** The pebbling number of [G] is [N]: the least number of pebbles such that a pebble can be
    brought to any vertex from any distribution. *)
Definition pebbling_number (G : sgraph) (N : nat) : Prop :=
  (forall D : G -> nat, \sum_(v : G) D v = N -> forall r : G, pebble_solvable D r) /\
  (forall M : nat,
     (forall D : G -> nat, \sum_(v : G) D v = M -> forall r : G, pebble_solvable D r) ->
     N <= M).

(** ** Hat guessing *)

(** Strategies of the players, who are the vertices: their guesses in [q] colours. *)
Definition hat_strategy (G : sgraph) (q : nat) : Type :=
  G -> {ffun G -> 'I_q} -> 'I_q.

(** Each guess depends only on the colours of the neighbours. *)
Definition sees_only_neighbors (G : sgraph) (q : nat)
    (s : hat_strategy G q) : Prop :=
  forall (v : G) (c c' : {ffun G -> 'I_q}),
    (forall u : G, u -- v -> c u = c' u) -> s v c = s v c'.

(** Some strategy ensures at least one correct guess with [q] colours. *)
Definition hat_guessing_win (G : sgraph) (q : nat) : Prop :=
  exists s : hat_strategy G q,
    sees_only_neighbors s /\
    forall c : {ffun G -> 'I_q}, exists v : G, s v c = c v.

(** The hat guessing number of [G] is at most [m]. *)
Definition hat_guessing_number_le (G : sgraph) (m : nat) : Prop :=
  forall q : nat, hat_guessing_win G q -> (q <= m)%N.

(** ** Cops and robbers *)

Section CopsAndRobbers.
Variable G : sgraph.

(** The positions of [k] cops. *)
Definition cop_position (k : nat) := {ffun 'I_k -> G}.

(** Some cop is on the vertex [r] of the robber. *)
Definition captured (k : nat) (C : cop_position k) (r : G) : bool :=
  [exists i : 'I_k, C i == r].

(** A move of the cops: each one stays or goes to a neighbour. *)
Definition cop_move (k : nat) (C C' : cop_position k) : bool :=
  [forall i : 'I_k, C i -*- C' i].

(** The cops, who play first, capture the robber in at most [t] rounds. *)
Fixpoint cops_capture (k t : nat) (C : cop_position k) (r : G) {struct t} : bool :=
  captured C r ||
  (if t is t'.+1 then
     [exists C' : cop_position k,
        cop_move C C' &&
        (captured C' r ||
         [forall r' : G, r -*- r' ==> cops_capture t' C' r'])]
   else false).

(** For some initial position, [k] cops win in at most [t] rounds. *)
Definition cops_win_within (k t : nat) : bool :=
  [exists C0 : cop_position k, [forall r0 : G, cops_capture t C0 r0]].

(** [k] cops win. *)
Definition cops_win (k : nat) : Prop := exists t : nat, cops_win_within k t.

(** The cop number of [G] is at most [k]. *)
Definition cop_number_le (k : nat) : Prop := exists j : nat, (j <= k)%N /\ cops_win j.

End CopsAndRobbers.

(** ** Zombies and survivors

    As cops and robbers, but the zombies must approach the survivor at each move ([G] is
    connected).  Positions, captures and moves of the survivor are those of the previous game. *)

Section ZombiesAndSurvivors.
Variable G : sgraph.

(** A move of the zombies: each one goes to a neighbour closer to [s]. *)
Definition zombie_move (k : nat) (s : G) (Z Z' : cop_position G k) : bool :=
  [forall i : 'I_k, (Z i -- Z' i) && (graph_dist (Z' i) s < graph_dist (Z i) s)].

(** The zombies can capture the survivor in at most [t] rounds. *)
Fixpoint zombies_capture (k t : nat) (Z : cop_position G k) (s : G) {struct t} : bool :=
  captured Z s ||
  (if t is t'.+1 then
     [exists Z' : cop_position G k,
        zombie_move s Z Z' &&
        (captured Z' s ||
         [forall s' : G, s -*- s' ==> zombies_capture t' Z' s'])]
   else false).

(** For some initial position, [k] zombies win in at most [t] rounds. *)
Definition zombies_win_within (k t : nat) : bool :=
  [exists Z0 : cop_position G k, [forall s0 : G, zombies_capture t Z0 s0]].

(** [k] zombies win. *)
Definition zombies_win (k : nat) : Prop := exists t : nat, zombies_win_within k t.

(** The zombie number of [G] is [k]: the minimum number of zombies that win. *)
Definition zombie_number (k : nat) : Prop :=
  zombies_win k /\ forall j : nat, j < k -> ~ zombies_win j.

End ZombiesAndSurvivors.

(** ** Multistage networks

    A network with [s] stages consists of [s] copies of the same bipartite graph, which joins
    [t] inputs to [t] outputs by the relation [S]. *)

(** [m] is a mask: the edge [(i, a)] joins the input [i] of the first stage to the output
    [m (i, a)] of the last one, and each output of the last stage has degree [k]. *)
Definition is_mask (t k : nat) (m : 'I_t * 'I_k -> 'I_t) : Prop :=
  forall j : 'I_t, #|[set x | m x == j]| = k.

(** The paths [route x] through [s] stages connect the ends of the edges [x] of the mask [m], and
    they are edge-disjoint. *)
Definition mask_routing (t k : nat) (S : rel 'I_t) (s : nat) (m : 'I_t * 'I_k -> 'I_t)
  (route : 'I_t * 'I_k -> nat -> 'I_t) : Prop :=
  [/\ forall x, route x 0 = x.1,
      forall x, route x s = m x,
      forall x q, q < s -> S (route x q) (route x q.+1) &
      forall x y q, q < s ->
        route x q = route y q -> route x q.+1 = route y q.+1 -> x = y].

(** The network with [s] stages is rearrangeable: every mask has a routing (the bipartite graph
    is meant to be [k]-regular). *)
Definition mask_rearrangeable (t k : nat) (S : rel 'I_t) (s : nat) : Prop :=
  forall m : 'I_t * 'I_k -> 'I_t, is_mask m -> exists route, mask_routing S s m route.

(** ** Lemmas on the edges of walks and cycles *)

Section EdgeLists.
Variable T : finType.
Implicit Types (s t c : seq T) (x y : T).

Lemma seq_edge_list_cons x y s :
  seq_edge_list (x :: y :: s) = [set x; y] :: seq_edge_list (y :: s).
Proof. by []. Qed.

Lemma seq_edge_list_cat x s t :
  seq_edge_list (x :: s ++ t) = seq_edge_list (x :: s) ++ seq_edge_list (last x s :: t).
Proof. by elim: s x => //= y s IHs x; rewrite !seq_edge_list_cons IHs. Qed.

Lemma seq_edge_list_rcons x s y :
  seq_edge_list (x :: rcons s y) = rcons (seq_edge_list (x :: s)) [set last x s; y].
Proof. by rewrite -!cats1 seq_edge_list_cat. Qed.

Lemma seq_edge_list_rev s : seq_edge_list (rev s) = rev (seq_edge_list s).
Proof.
elim: s => // x [|y s] // IHs.
rewrite rev_cons; case def_t: (rev (y :: s)) IHs => [|z t] IHs.
  by move/(congr1 size): def_t; rewrite size_rev.
have e : last z t = y by rewrite -(last_cons x) -def_t rev_cons last_rcons.
by rewrite rcons_cons seq_edge_list_rcons IHs e setUC seq_edge_list_cons rev_cons.
Qed.

(** The edges of a walk join vertices of this walk. *)
Lemma mem_seq_edge_list s e x : e \in seq_edge_list s -> x \in e -> x \in s.
Proof.
elim: s => // y [|z s] // IHs; rewrite seq_edge_list_cons inE => /predU1P[->|es xe].
  by case/set2P=> ->; rewrite !inE eqxx ?orbT.
by rewrite inE IHs ?orbT.
Qed.

Lemma seq_cycle_edge_list_cons x s :
  seq_cycle_edge_list (x :: s) = seq_edge_list (x :: rcons s x).
Proof.
rewrite /seq_cycle_edge_list rot1_cons /seq_edge_list /=; congr map.
by elim: s {1 3}x => //= y s IHs z; rewrite IHs.
Qed.

Lemma seq_cycle_edge_list_cat x s y t :
  seq_cycle_edge_list (x :: s ++ y :: t) =
  seq_edge_list (x :: rcons s y) ++ seq_edge_list (y :: rcons t x).
Proof.
by rewrite seq_cycle_edge_list_cons rcons_cat -cat_rcons seq_edge_list_cat last_rcons.
Qed.

Lemma perm_seq_cycle_edge_list_rot n c :
  perm_eq (seq_cycle_edge_list (rot n c)) (seq_cycle_edge_list c).
Proof.
rewrite /rot -[c in X in perm_eq _ X](cat_take_drop n c).
case: (take n c) (drop n c) => [|x s] [|y t]; rewrite ?cats0 //.
by rewrite !cat_cons !seq_cycle_edge_list_cat perm_catC.
Qed.

End EdgeLists.

Lemma chordless_cycle_rot (G : sgraph) n (c : seq G) :
  chordless_cycle c -> chordless_cycle (rot n c).
Proof.
case=> sc ch; split; first by rewrite /seq_cycle /ucycleb rot_cycle rot_uniq size_rot.
by move=> u v; rewrite !mem_rot (perm_mem (perm_seq_cycle_edge_list_rot _ _)); apply: ch.
Qed.

(** ** Degrees in cycles *)

(** A cycle contains at least two neighbours of each of its vertices. *)
Lemma seq_cycle_degree (G : sgraph) (c : seq G) v :
  seq_cycle (--) c -> v \in c -> 1 < #|N(v) :&: [set:: c]|.
Proof.
move=> /andP[/andP[cyc uc] sz] /rot_to[i s e].
move: cyc uc sz; rewrite -(rot_cycle i) -(rot_uniq i) -(size_rot i) e.
have memE x : (x \in [set:: c]) = (x \in v :: s) by rewrite inE -e mem_rot.
case: s e memE => [|x [|y s]] //= _ memE; rewrite rcons_path.
move=> /and3P[vx _ /andP[_ lv]] /and3P[_ xs _] _.
have sub : [set x; last y s] \subset N(v) :&: [set:: c].
  rewrite subUset !sub1set !in_setI !memE !in_opn vx sg_sym lv /=.
  by rewrite in_cons mem_head orbT 2!(in_cons _ _ (last _ _)) mem_last !orbT.
apply: leq_trans (subset_leq_card sub); rewrite cards2.
by case: eqP xs => // ->; rewrite mem_last.
Qed.

(** ** Holes *)

Lemma nth_rot1 (T : Type) (x0 : T) c k : k < size c ->
  nth x0 (rot 1 c) k = nth x0 c (k.+1 %% size c).
Proof.
case: c => [//|x p] /=; rewrite rot1_cons nth_rcons ltnS leq_eqVlt.
by case: eqP => [->|_ /= lt_k]; [rewrite ltnn modnn|rewrite lt_k modn_small].
Qed.

Section Holes.
Variable G : sgraph.
Implicit Types (c : seq G) (u : G).

Lemma hole_rot i c : hole c -> hole (rot i c).
Proof. by case=> /chordless_cycle_rot ch s4; split; rewrite ?size_rot. Qed.

(** A hole can be listed from any of its vertices. *)
Lemma hole_mem_rot c u : hole c -> u \in c ->
  exists2 p, hole (u :: p) & size (u :: p) = size c.
Proof. by move=> hc /rot_to [i p e]; exists p; rewrite -e ?size_rot //; apply: hole_rot. Qed.

(** The edges of a cycle in terms of indices. *)
Lemma seq_cycle_edge_list_nth (x0 : G) c i j : uniq c -> i < size c -> j < size c ->
  ([set nth x0 c i; nth x0 c j] \in seq_cycle_edge_list c)
  = (i.+1 %% size c == j) || (j.+1 %% size c == i).
Proof.
move=> uc lt_i lt_j; have s1 : size c = size (rot 1 c) by rewrite size_rot.
have edge k : k < size c ->
    [set nth x0 c k; nth x0 c (k.+1 %% size c)] \in seq_cycle_edge_list c.
  move=> lt_k; apply/mapP; exists (nth x0 c k, nth x0 (rot 1 c) k); last by rewrite nth_rot1.
  by rewrite -nth_zip //; apply: mem_nth; rewrite size_zip -s1 minnn.
apply/idP/idP => [|/orP [/eqP<-|/eqP<-]]; [|exact: edge|by rewrite setUC; apply: edge].
case/mapP => p /(nthP (x0, x0)) [k]; rewrite size_zip -s1 minnn => lt_k <-.
rewrite nth_zip // nth_rot1 //= => /doubleton_eq_iff.
have lt_k' : k.+1 %% size c < size c by rewrite ltn_pmod // (leq_ltn_trans _ lt_k).
case=> -[/eqP e /eqP e']; move: e e'; rewrite !nth_uniq // => /eqP-> /eqP->; rewrite eqxx ?orbT //.
Qed.

(** In a hole, the adjacent vertices are the consecutive ones. *)
Lemma hole_nthP (x0 : G) c : hole c <->
  [/\ uniq c, 3 < size c
    & forall i j, i < size c -> j < size c ->
        (nth x0 c i -- nth x0 c j)
        = (i.+1 %% size c == j) || (j.+1 %% size c == i)].
Proof.
have cycleP : path.cycle (--) c <->
    forall k, k < size c -> nth x0 c k -- nth x0 c (k.+1 %% size c).
  have E k : k < size c -> (nth x0 c k -- nth x0 c (k.+1 %% size c))
                         = (nth x0 c k -- nth x0 (rot 1 c) k) by move=> /(nth_rot1 x0) ->.
  case: c E => [|x p E]; first by [].
  rewrite /path.cycle; split=> [/(pathP x0) H k lt_k|H].
    have := H k; rewrite E // rot1_cons size_rcons -rcons_cons nth_rcons lt_k; exact.
  apply/(pathP x0) => k; rewrite size_rcons => lt_k.
  by rewrite -rcons_cons nth_rcons lt_k -rot1_cons -E // H.
split=> [[[/andP [/andP [/cycleP cyc uc] _] ch] s4]|[uc s4 adj]].
- split=> // i j lt_i lt_j; apply/idP/idP => [/ch|].
    by rewrite !mem_nth // seq_cycle_edge_list_nth //; apply.
  by case/orP => /eqP <-; [|rewrite sg_sym]; apply: cyc.
- split=> //; split; first rewrite /seq_cycle /ucycleb uc (ltnW s4) !andbT.
    by apply/cycleP => k lt_k; rewrite adj ?eqxx ?ltn_pmod // (leq_ltn_trans _ lt_k).
  move=> u v /(nthP x0) [i lt_i <-] /(nthP x0) [j lt_j <-].
  by rewrite adj // seq_cycle_edge_list_nth.
Qed.

End Holes.

(** ** Induced paths and cycles *)

Section InducedPaths.
Variable G : sgraph.
Implicit Types (s : seq G) (x y z u v : G).

Lemma chordless_path_cons x y s :
  chordless_path (x :: y :: s) <->
  [/\ x -- y, x \notin y :: s, {in s, forall z, ~~ (x -- z)} & chordless_path (y :: s)].
Proof.
split=> [[/andP[xs us] /andP[xy ps] ch]|[xy xs nadj [us ps ch]]].
- have memS z : z \in y :: s -> z \in x :: y :: s by rewrite [z \in x :: _]inE orbC => ->.
  split=> // [z zs|]; first apply/negP => xz.
    have zys : z \in y :: s by rewrite inE zs orbT.
    have := ch x z (mem_head _ _) (memS z zys) xz; rewrite seq_edge_list_cons inE.
    case/predU1P=> [/setP/(_ z)|/mem_seq_edge_list/(_ (set21 _ _))]; last by rewrite (negbTE xs).
    rewrite set22 !inE => /esym/orP[]/eqP e; first by rewrite e sg_irrefl in xz.
    by case/andP: us; rewrite -e zs.
  split=> // u v uys vys uv.
  have := ch u v (memS u uys) (memS v vys) uv; rewrite seq_edge_list_cons inE.
  by case/predU1P=> // /setP/(_ x); rewrite set21 => /set2P[]e; rewrite e ?uys ?vys in xs.
- split=> [||u v]; [exact/andP|exact/andP|].
  have nx z : z \in y :: s -> x -- z -> z = y.
    by rewrite inE => /predU1P[//|/nadj/negbTE ->].
  rewrite seq_edge_list_cons ![_ \in x :: _]inE.
  move=> /predU1P[->|uys] /predU1P[->|vys] uv; rewrite inE; first by rewrite sg_irrefl in uv.
  + by rewrite (nx v) ?eqxx.
  + by rewrite (nx u) 1?sg_sym // setUC eqxx.
  + by rewrite ch ?orbT.
Qed.

(** [chordless_path] as a Boolean. *)
Fixpoint chordless_pathb s : bool :=
  if s is x :: t then
    if t is y :: s' then
      [&& x -- y, x \notin t, all (fun z => ~~ (x -- z)) s' & chordless_pathb t]
    else true
  else true.

Lemma chordless_pathP s : reflect (chordless_path s) (chordless_pathb s).
Proof.
elim: s => [|x [|y s] IHs]; [by left|left; split=> // u v|].
  by rewrite !inE => /eqP-> /eqP->; rewrite sg_irrefl.
apply: (iffP and4P) => [[xy xs /allP nadj /IHs ch]|/chordless_path_cons[xy xs nadj /IHs ch]].
  exact/chordless_path_cons.
by split=> //; apply/allP.
Qed.

End InducedPaths.

(** An induced cycle contains exactly two neighbours of each of its vertices. *)
Lemma chordless_cycle_degree (G : sgraph) (c : seq G) v :
  chordless_cycle c -> v \in c -> #|N(v) :&: [set:: c]| = 2.
Proof.
move=> cc vc; have [sc _] := cc; apply/eqP; rewrite eqn_leq seq_cycle_degree // andbT.
have [i s e] := rot_to vc; have := chordless_cycle_rot i cc; rewrite e => -[{}sc ch].
apply: leq_trans (_ : #|[set head v s; last v s]| <= 2); last by rewrite cards2; case: eqP.
apply/subset_leq_card/subsetP => u.
rewrite in_setI in_opn in_set -(mem_rot i) e => /andP[vu us].
have := ch v u (mem_head _ _) us vu; rewrite seq_cycle_edge_list_cons.
have nuv : u != v by apply: contraTneq vu => ->; rewrite sg_irrefl.
case: s sc {ch e} us => [|x s] /andP[/andP[_]] //= /andP[vs _] _ us.
rewrite seq_edge_list_cons -rcons_cons seq_edge_list_rcons inE mem_rcons inE.
case/or3P=> [/eqP/setP/(_ u)|/eqP/setP/(_ u)|/mem_seq_edge_list/(_ (set21 _ _))].
- by rewrite set22 !inE (negbTE nuv) => /esym/eqP->; rewrite eqxx.
- by rewrite set22 !inE (negbTE nuv) orbF => /esym/eqP->; rewrite eqxx orbT.
- by rewrite (negbTE vs).
Qed.
