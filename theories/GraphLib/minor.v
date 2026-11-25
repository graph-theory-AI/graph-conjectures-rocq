(** * Minors, subdivisions, immersions, vertex-minors and width parameters

Minors ([minor G H] : [H] is a minor of [G]) and tree decompositions ([sdecomp]) are those of
GraphTheory; the index graph of a tree decomposition is a forest. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring minor treewidth.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Minors *)

(** The class [C] excludes some graph as a minor. *)
Definition excludes_a_minor (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

(** [H] is a minor of [G] at depth [r]: the branch sets have radius at most [r]. *)
Definition shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists2 B : H -> {set G}, minor_rmap B &
    forall x : H, exists c : induced (B x), ball r c = [set: induced (B x)].

(** The class [C] has bounded expansion: the average degree of its minors at depth [r] is bounded
    by a function of [r]. *)
Definition bounded_expansion (C : sgraph -> Prop) : Prop :=
  exists f : nat -> nat, forall (r : nat) (G H : sgraph),
    C G -> shallow_minor G H r -> 2 * #|E(H)| <= f r * #|H|.

(** The class [C] has polynomial expansion: the edge density of its minors at depth [r] is
    bounded by a polynomial in [r] (given by the list [p] of its coefficients). *)
Definition polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        shallow_minor G H r -> #|E(H)| <= horner_rec p r * #|H|.

(** The Hadwiger number of [G] is [h]. *)
Definition hadwiger_number (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\ (forall h', minor G 'K_h' -> (h' <= h)%N).

(** [B] and [w] are a fractional clique minor of [G] of value [r]: the branch sets [B i] are
    nonempty and connected, there is an edge between any two of them (they may overlap), and the
    sum of the weights of those containing a given vertex is at most 1. *)
Definition fractional_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, (0 <= w i)%R),
      (forall i, B i != set0 /\ connected (B i)),
      (forall i j, i != j -> neighbor (B i) (B j)),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & (r = \sum_i w i)%R].

(** The fractional Hadwiger number of [G] is [r]. *)
Definition fractional_hadwiger_number (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), fractional_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     fractional_clique_minor B w r' -> (r' <= r)%R).

(** [H] is an odd minor of [G]: for some 2-colouring [sigma] of the vertices of [G], it has a
    model in which the branch sets are connected by bichromatic edges, and the edges of [H] are
    realised by monochromatic edges. *)
Definition odd_minor (G H : sgraph) : Prop :=
  exists (B : H -> {set G}) (sigma : G -> bool),
    [/\ forall x : H, B x != set0,
        forall (x : H) (u v : G), u \in B x -> v \in B x ->
          connect (fun a b : G => [&& a \in B x, b \in B x, a -- b & sigma a != sigma b]) u v,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y ->
          exists u v : G, [/\ u \in B x, v \in B y, u -- v & sigma u == sigma v]].

(** ** Immersions *)

(** [G] contains an immersion of [H]: [f] maps the vertices of [H] to distinct vertices of [G],
    and the edges [u v] of [H] are mapped to pairwise edge-disjoint walks from [f u] to [f v]. *)
Definition immersion (G H : sgraph) : Prop :=
  exists (f : H -> G) (P : H -> H -> seq G),
    injective f /\
    (forall u v : H, u -- v ->
        path sedge (f u) (P u v) /\ last (f u) (P u v) = f v) /\
    (forall u1 v1 u2 v2 : H, u1 -- v1 -> u2 -- v2 ->
        [set u1; v1] != [set u2; v2] ->
        [disjoint seq_edge_set (f u1 :: P u1 v1)
                & seq_edge_set (f u2 :: P u2 v2)]).

(** ** Subdivisions *)

(** Subdivisions of [H] in [G]: distinct branch vertices and, for each edge of [H], the list of
    the inner vertices of a path between its branch vertices (reversed for the opposite
    direction).  Inner vertices are not branch vertices, and the paths of distinct edges have no
    common inner vertex. *)
Record subdivision_model (H G : sgraph) := SubdivisionModel {
  subdiv_branch : H -> G;
  subdiv_branch_inj : injective subdiv_branch;
  subdiv_path : H -> H -> seq G;
  subdiv_pathP : forall u v : H, u -- v ->
      upath (subdiv_branch u) (subdiv_branch v) (rcons (subdiv_path u v) (subdiv_branch v));
  subdiv_pathC : forall u v : H, u -- v -> subdiv_path v u = rev (subdiv_path u v);
  subdiv_path_branch : forall (u v w : H) (x : G),
      u -- v -> x \in subdiv_path u v -> x != subdiv_branch w;
  subdiv_path_disjoint : forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' -> x \in subdiv_path u v -> x \in subdiv_path u' v' ->
      [set u; v] = [set u'; v']
}.

(** [G] contains a subdivision of [H] ([H] is a topological minor of [G]). *)
Definition has_subdivision (G H : sgraph) : Prop := inhabited (subdivision_model H G).

Section SubdivisionOf.
Variables (K H : sgraph) (m : subdivision_model K H).

(** [x] is a vertex of the subdivision. *)
Definition subdiv_vertex (x : H) : Prop :=
  (exists h : K, subdiv_branch m h = x) \/ (exists u v : K, u -- v /\ x \in subdiv_path m u v).

(** [x y] is an edge of the subdivision. *)
Definition subdiv_edge (x y : H) : Prop :=
  exists u v : K, u -- v /\
    [set x; y] \in
      seq_edge_list (subdiv_branch m u :: rcons (subdiv_path m u v) (subdiv_branch m v)).

(** The subdivision has all the vertices and edges of [H]. *)
Definition subdiv_spans : Prop :=
  (forall x : H, subdiv_vertex x) /\ (forall x y : H, x -- y -> subdiv_edge x y).

End SubdivisionOf.

(** [H] is a subdivision of [K]. *)
Definition is_subdivision_of (H K : sgraph) : Prop :=
  exists m : subdivision_model K H, subdiv_spans m.

(** ** Walls, thetas, prisms, wheels *)

(** The edges of the wall, in one direction: those of the rows of the grid, and every other edge
    of its columns. *)
Definition wall_rel (t : nat) (u v : 'I_t * 'I_t) : bool :=
  ((u.1 == v.1) && ((u.2 : nat).+1 == v.2)) ||
  [&& (u.2 : nat) == v.2, (u.1 : nat).+1 == v.1 & ~~ odd ((u.1 : nat) + u.2)].

(** The wall obtained from the grid with [t] rows and [t] columns. *)
Definition wall (t : nat) : sgraph := sgraph_of_rel (@wall_rel t).

(** [H] is a theta: a subdivision of [K_2,3]. *)
Definition is_theta (H : sgraph) : Prop := is_subdivision_of H (KB 2 3).

(** [H] is a prism, in the sense of three-path configurations: a subdivision of the prism on 6
    vertices (two triangles joined by three edges), where the edges of the triangles are not
    subdivided. *)
Definition prism_subdivision (H : sgraph) : Prop :=
  exists m : subdivision_model (cartesian_product 'K_3 'K_2) H,
    subdiv_spans m /\
    forall (u v : cartesian_product 'K_3 'K_2),
      u -- v -> u.2 == v.2 -> subdiv_path m u v = [::].

(** [G] has no even wheel: no vertex outside a hole has an even number, at least 3, of
    neighbours in the hole. *)
Definition even_wheel_free (G : sgraph) : Prop :=
  forall (v : G) (c : seq G),
    hole c -> v \notin c -> 3 <= #|N(v) :&: [set:: c]| -> odd #|N(v) :&: [set:: c]|.

(** The induced biclique number of [G] is [t]: [t] is maximum such that [G] has an induced
    subgraph isomorphic to [K_t,t]. *)
Definition induced_biclique_number (G : sgraph) (t : nat) : Prop :=
  has_induced_copy G (KB t t) /\
  forall s : nat, has_induced_copy G (KB s s) -> s <= t.

(** ** Tree decompositions *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** The treewidth of [G] is at least [k]. *)
Definition treewidth_ge (G : sgraph) (k : nat) : Prop :=
  forall m : nat, treewidth_le G m -> k <= m.

(** The tree-independence number of [G] is at most [k]. *)
Definition tree_independence_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ forall t : T, α(D t) <= k.

(** [M] is an induced matching: the ends of distinct edges are distinct and non-adjacent. *)
Definition induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  {subset M <= E(G)} /\
  forall (e f : {set G}) (x y : G),
    e \in M -> f \in M -> e != f -> x \in e -> y \in f -> (x != y) && ~~ (x -- y).

(** The induced matching treewidth of [G] is at most [m]: for some tree decomposition, each
    induced matching whose edges all meet a same bag has at most [m] edges. *)
Definition induced_matching_tw_le (G : sgraph) (m : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\
    forall M : {set {set G}},
      induced_matching M ->
      (exists t : T, forall e : {set G}, e \in M -> exists2 x : G, x \in e & x \in D t) ->
      #|M| <= m.

(** [L] is a layering: adjacent vertices are in the same layer or in consecutive layers. *)
Definition layering (G : sgraph) (L : G -> nat) : Prop :=
  forall u v : G, u -- v -> (L u <= (L v).+1) /\ (L v <= (L u).+1).

(** The layered treewidth of [G] is at most [l]. *)
Definition layered_treewidth_le (G : sgraph) (l : nat) : Prop :=
  exists (L : G -> nat) (T : forest) (D : T -> {set G}),
    [/\ layering L, sdecomp T G D &
        forall (t : T) (i : nat), #|[set v in D t | L v == i]| <= l].

(** ** Tree-depth *)

(** [rank] is a vertex ranking: each walk between distinct vertices of the same rank contains a
    vertex of larger rank. *)
Definition vertex_ranking (G : sgraph) (k : nat) (rank : G -> 'I_k) : Prop :=
  forall (x y : G) (p : seq G),
    x != y ->
    path (--) x p ->
    last x p = y ->
    rank x = rank y ->
    exists z : G, z \in p /\ rank x < rank z.

(** The tree-depth of [G] is at most [k]. *)
Definition treedepth_le (G : sgraph) (k : nat) : Prop :=
  exists rank : G -> 'I_k, vertex_ranking rank.

(** The connected tree-depth of [G] is at most [k]: [G] is a subgraph of the closure of a rooted
    tree of depth at most [k]. *)
Definition connected_treedepth_le (G : sgraph) (k : nat) : Prop :=
  0 < k /\ exists r : G, treedepth_le (induced (~: [set r])) k.-1.

(** ** Twin-width *)

(** There are both edges and non-edges from [X] to [Y]. *)
Definition red_pair (G : diGraph) (X Y : {set G}) : bool :=
  [exists x in X, exists y in Y, x -- y] && [exists x in X, exists y in Y, ~~ (x -- y)].

(** The red degree of the part [X] of [P]. *)
Definition red_degree (G : diGraph) (P : {set {set G}}) (X : {set G}) : nat :=
  #|[set Y in P | (Y != X) && (red_pair X Y || red_pair Y X)]|.

(** The partition into singletons. *)
Definition singletons (G : diGraph) : {set {set G}} := [set [set x] | x : G].

(** [Q] is obtained from [P] by merging two parts. *)
Definition merge_parts (G : diGraph) (P Q : {set {set G}}) : bool :=
  [exists X in P, exists Y in P, (X != Y) && (Q == (X :|: Y) |: (P :\ X :\ Y))].

(** The twin-width of the graph or digraph [G] is at most [d]: some sequence of merges from the
    partition into singletons to a single part has red degrees at most [d]. *)
Definition twin_width_le (G : diGraph) (d : nat) : Prop :=
  exists s : seq {set {set G}},
    [/\ path (@merge_parts G) (singletons G) s,
        #|last (singletons G) s| <= 1 &
        forall P : {set {set G}},
          P \in (singletons G :: s) ->
          forall X : {set G}, X \in P -> red_degree P X <= d].

(** The twin-width of [G] is [t]. *)
Definition twin_width (G : diGraph) (t : nat) : Prop :=
  twin_width_le G t /\ forall m : nat, m < t -> ~ twin_width_le G m.

(** ** Clique-width *)

(** Expressions for labelled graphs: one vertex, disjoint union, all edges between two labels,
    relabelling. *)
Inductive clique_width_expr : Type :=
| CwLeaf of nat
| CwUnion of clique_width_expr & clique_width_expr
| CwJoin of nat & nat & clique_width_expr
| CwRelab of nat & nat & clique_width_expr.

(** The labels of the vertices, which are the leaves of the expression from left to right. *)
Fixpoint cw_labels (e : clique_width_expr) : seq nat :=
  match e with
  | CwLeaf i => [:: i]
  | CwUnion a b => cw_labels a ++ cw_labels b
  | CwJoin _ _ a => cw_labels a
  | CwRelab i j a => [seq (if l == i then j else l) | l <- cw_labels a]
  end.

(** The edges of the graph of the expression. *)
Fixpoint cw_edge (e : clique_width_expr) (x y : nat) : bool :=
  match e with
  | CwLeaf _ => false
  | CwUnion a b =>
      let n := size (cw_labels a) in
      if (x < n) && (y < n) then cw_edge a x y
      else if (n <= x) && (n <= y) then cw_edge b (x - n) (y - n)
      else false
  | CwJoin i j a =>
      let L := cw_labels a in
      cw_edge a x y ||
      [&& x != y, x < size L, y < size L &
          ((nth 0 L x == i) && (nth 0 L y == j)) ||
          ((nth 0 L x == j) && (nth 0 L y == i))]
  | CwRelab _ _ a => cw_edge a x y
  end.

(** The expression uses labels less than [k]. *)
Fixpoint cw_well_formed (k : nat) (e : clique_width_expr) : bool :=
  match e with
  | CwLeaf i => i < k
  | CwUnion a b => cw_well_formed k a && cw_well_formed k b
  | CwJoin i j a => [&& i < k, j < k, i != j & cw_well_formed k a]
  | CwRelab i j a => [&& i < k, j < k & cw_well_formed k a]
  end.

(** [G] is the graph of the expression [e]. *)
Definition cw_realizes (e : clique_width_expr) (G : sgraph) : Prop :=
  exists f : G -> nat,
    [/\ injective f,
        forall v : G, f v < size (cw_labels e),
        forall i : nat, i < size (cw_labels e) -> exists v : G, f v = i &
        forall u v : G, (u -- v) = cw_edge e (f u) (f v)].

(** The clique-width of [G] is at most [k] ([G] is nonempty). *)
Definition clique_width_le (G : sgraph) (k : nat) : Prop :=
  exists e : clique_width_expr, cw_well_formed k e /\ cw_realizes e G.

(** ** Vertex-minors *)

(** The local complement of [G] at [v]: the edges are complemented in the neighbourhood of [v]. *)
Definition local_complement (G : sgraph) (v : G) : sgraph :=
  sgraph_of_rel (fun x y : G => (x -- y) (+) ((x -- v) && (y -- v))).

(** [vertex_minor G H]: [H] is a vertex-minor of [G], obtained by local complementations and
    vertex deletions (up to isomorphism). *)
Inductive vertex_minor : sgraph -> sgraph -> Prop :=
| vertex_minor_refl (G : sgraph) : vertex_minor G G
| vertex_minor_lc (G H K : sgraph) (v : H) :
    vertex_minor G H -> (local_complement v ≃ K) -> vertex_minor G K
| vertex_minor_del (G H K : sgraph) (v : H) :
    vertex_minor G H -> (induced [set~ v] ≃ K) -> vertex_minor G K.

(** The class [F] is closed under vertex-minors. *)
Definition vertex_minor_closed (F : sgraph -> Prop) : Prop :=
  forall G H : sgraph, F G -> vertex_minor G H -> F H.
