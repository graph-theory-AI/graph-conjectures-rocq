(** * Minors, subdivisions, immersions, vertex-minors and width parameters

Minors ([minor G H] : [H] is a minor of [G]) and tree decompositions ([sdecomp]) are those of
GraphTheory; the index graph of a tree decomposition is a forest. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring minor treewidth.
From mathcomp Require Import boot order ssralg ssrnum ssrint rat poly.
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

(** ** Holes in induced subgraphs, line graphs and subdivisions *)

Section Sequences.
Variable T : eqType.
Implicit Types (c s : seq T) (x : T).

(** The pairs of consecutive elements of [x :: s] are related by a path [x :: s] of [r]. *)
Lemma path_zip (r : rel T) x s p : path r x s -> p \in zip (x :: s) s -> r p.1 p.2.
Proof.
by elim: s x => //= y s IHs x /andP[xy ys]; rewrite inE => /predU1P[-> //|]; apply: IHs.
Qed.

(** In a cyclic sequence without repetition and of length at least 3, the successor of the
    successor of [x] is not [x]. *)
Lemma next_next_neq c x : uniq c -> 2 < size c -> x \in c -> next c (next c x) != x.
Proof.
move=> uc c3 /rot_to[i s e]; rewrite -!(next_rot i uc) e.
move: c3 uc; rewrite -(size_rot i) -(rot_uniq i) e.
case: s {e} => [|y [|z s]] //= _ /andP[]; rewrite !inE !negb_or => /and3P[xy xz _] _.
by rewrite eqxx (eq_sym y x) (negbTE xy) eqxx eq_sym.
Qed.

Lemma uniq_flatten_map (U : eqType) (f : T -> seq U) s :
  uniq s -> {in s, forall x, uniq (f x)} ->
  {in s &, forall x y z, z \in f x -> z \in f y -> x = y} -> uniq (flatten (map f s)).
Proof.
elim: s => //= x s IHs /andP[xs us] uf dj; rewrite cat_uniq uf ?mem_head //=.
have sub : {subset s <= x :: s} by move=> y ys; rewrite inE ys orbT.
rewrite IHs ?andbT //.
- by move=> y ys; apply/uf/sub.
- by move=> y y' ys y's; apply: dj; apply: sub.
apply/hasPn => z /flattenP[_ /mapP[y ys ->] zy]; apply/negP => zx.
by move: xs; rewrite (dj x y (mem_head _ _) (sub _ ys) z zx zy) ys.
Qed.

End Sequences.

(** The steps [p] of a cycle [x :: s] of [G]: [p.2] is the successor of [p.1]. *)
Lemma cycle_pairs (G : sgraph) (x : G) s p :
  cycle (--) (x :: s) -> uniq (x :: s) -> p \in zip (x :: rcons s x) (rcons s x) ->
  [/\ p.1 -- p.2, next (x :: s) p.1 = p.2 & p.1 \in x :: s].
Proof.
move=> cyc uc pz.
have := cycle_next uc; rewrite -[fcycle _ _]andTb -cyc -cycle_relI.
move=> /path_zip/(_ pz)/andP[p12 /eqP np]; split=> //; apply: contraTT p12 => pc.
by rewrite -np next_nth (negbTE pc) sg_irrefl.
Qed.

(** A closed walk [x :: s] ending at [x] has the edges of the cycle [s]. *)
Lemma seq_cycle_edge_list_last (T : finType) (x : T) s :
  s != [::] -> last x s = x -> seq_cycle_edge_list s =i seq_edge_list (x :: s).
Proof.
case/lastP: s => [//|s y] _; rewrite last_rcons => -> e.
rewrite -[in LHS]rot1_cons (perm_mem (perm_seq_cycle_edge_list_rot 1 _)).
by rewrite seq_cycle_edge_list_cons.
Qed.

Section HoleMaps.
Variables (G H : sgraph).

(** A map that is injective and preserves adjacency and non-adjacency on a hole maps it to a
    hole. *)
Lemma hole_map_in (f : G -> H) (c : seq G) :
  {in c &, injective f} -> {in c &, forall x y, (f x -- f y) = (x -- y)} ->
  hole c -> hole (map f c).
Proof.
case: c => [|x0 s] finj fE; first by case.
move/(hole_nthP x0) => [uc s4 adj]; apply/(hole_nthP (f x0)).
rewrite size_map map_inj_in_uniq //; split=> // i j ic jc.
by rewrite !(nth_map x0) // fE ?mem_nth // adj.
Qed.

Lemma hole_isubgraph (i : G ⇀ H) c : hole c -> hole (map i c).
Proof.
by apply: hole_map_in => x y _ _; [apply: isubgraph_inj | apply: isubgraph_mono].
Qed.

End HoleMaps.

(** The edges of a hole form a hole of the same length in the line graph. *)
Lemma hole_line_graph (W : sgraph) (c : seq W) :
  hole c -> exists2 d : seq (simple_line_graph W), hole d & size d = size c.
Proof.
case: c => [|x0 s]; first by case.
set c := x0 :: s => hc; have [[/andP[/andP[cyc uc] c3] ch] _] := hc.
have nx x : x \in c -> x -- next c x by apply: next_cycle.
have adjE x y : x \in c -> y \in c -> (x -- y) = (y == next c x) || (x == next c y).
  move=> xc yc; apply/idP/idP => [xy|/orP[]/eqP->]; rewrite ?nx // 1?sg_sym ?nx //.
  move: (ch x y xc yc xy); rewrite seq_cycle_edge_list_cons => /mapP[p pz].
  have [_ <- _] := cycle_pairs cyc uc pz.
  by case/doubleton_eq_iff => -[-> ->]; rewrite eqxx ?orbT.
have e0 : [set x0; next c x0] \in E(W) by rewrite in_edges nx ?mem_head.
clearbody c.
pose f x : simple_line_graph W := insubd (exist (fun e => e \in E(W)) _ e0) [set x; next c x].
have fv x : x \in c -> val (f x) = [set x; next c x].
  by move=> xc; rewrite insubdK ?in_edges ?nx.
have ninj := can_inj (prev_next uc).
have finj : {in c &, injective f}.
  move=> x y xc yc /(congr1 val); rewrite !fv // => /doubleton_eq_iff[[]//|[xy yx]].
  by have := next_next_neq uc c3 yc; rewrite -xy yx eqxx.
exists (map f c); last by rewrite size_map.
apply: hole_map_in hc => // x y xc yc.
have [<-|xy] := eqVneq x y; first by rewrite !sg_irrefl.
rewrite adjE // -[f x -- f y]/((val (f x) != val (f y)) && (val (f x) :&: val (f y) != set0)).
rewrite val_eqE (inj_in_eq finj) // xy /= !fv //.
apply/set0Pn/idP => [[z /setIP[]]|/orP[]/eqP->]; last 2 first.
- by exists (next c x); rewrite !inE !eqxx ?orbT.
- by exists (next c y); rewrite !inE !eqxx ?orbT.
rewrite !inE => /orP[]/eqP-> /orP[]/eqP; [by move/eqP: xy|move->|move<-|move/ninj/eqP];
  by rewrite ?eqxx ?orbT // (negbTE xy).
Qed.

Section SubdivisionHoles.
Variables (K W : sgraph) (m : subdivision_model K W).
Hypothesis spans : subdiv_spans m.
Local Abbreviation B := (subdiv_branch m).
Local Abbreviation P := (subdiv_path m).

(** The image of the walk [x :: s] of [K] in the subdivision, without its first vertex: for each
    step [u v], the inner vertices of the path of [u v], followed by the branch vertex of [v]. *)
Definition subdiv_walk (x : K) (s : seq K) : seq W :=
  flatten [seq rcons (P p.1 p.2) (B p.2) | p <- zip (x :: s) s].

Lemma subdiv_walk_cons x y s :
  subdiv_walk x (y :: s) = rcons (P x y) (B y) ++ subdiv_walk y s.
Proof. by []. Qed.

Lemma subdiv_walk_path x s : path (--) x s ->
  path (--) (B x) (subdiv_walk x s) /\ last (B x) (subdiv_walk x s) = B (last x s).
Proof.
elim: s x => [//|y s IHs] x /= /andP[xy /IHs[ps ls]].
have /andP[_ /andP[pxy _]] := subdiv_pathP m xy.
by rewrite subdiv_walk_cons cat_path last_cat last_rcons pxy ps ls.
Qed.

Lemma subdiv_walk_edges x s :
  seq_edge_list (B x :: subdiv_walk x s) =
  flatten [seq seq_edge_list (B p.1 :: rcons (P p.1 p.2) (B p.2)) | p <- zip (x :: s) s].
Proof.
by elim: s x => [//|y s IHs] x; rewrite subdiv_walk_cons seq_edge_list_cat last_rcons IHs.
Qed.

Lemma size_subdiv_walk x s :
  size (subdiv_walk x s) = size s + sumn [seq size (P p.1 p.2) | p <- zip (x :: s) s].
Proof.
elim: s x => [//|y s IHs] x; rewrite subdiv_walk_cons size_cat size_rcons IHs /=.
by rewrite addSn addnCA.
Qed.

(** The image of a hole [x :: s] of [K] in a subdivision [W] of [K] is a hole of [W]: as each
    edge of [W] lies on the path of an edge of [K], a chord of the image would come from a chord
    of the hole. *)
Theorem subdiv_hole x s : hole (x :: s) -> hole (subdiv_walk x (rcons s x)).
Proof.
move=> hc; have [[/andP[/andP[cyc uc] c3] chK] s4] := hc.
have [pI lI] := subdiv_walk_path cyc; rewrite last_rcons in lI.
set c := x :: s in hc cyc uc c3 chK s4 pI lI *.
set xs := rcons s x in cyc pI lI *; set I := subdiv_walk _ _ in pI lI *.
have pairsP := cycle_pairs cyc uc.
have pc p : p \in zip (x :: xs) xs -> p.1 \in c /\ p.2 \in c.
  by case/pairsP=> _ <-; rewrite mem_next.
have memI z : z \in I -> exists2 p, p \in zip (x :: xs) xs & z \in rcons (P p.1 p.2) (B p.2).
  by case/flattenP => _ /mapP[p pz ->]; exists p.
have pinj p q : p \in zip (x :: xs) xs -> q \in zip (x :: xs) xs -> p.2 = q.2 -> p = q.
  case: p q => [a b] [a' b'] /pairsP[_ /= <- _] /pairsP[_ /= <- _] e.
  by rewrite (can_inj (prev_next uc) e).
have uI : uniq I.
  apply: uniq_flatten_map; first by apply: zip_uniqr; rewrite rcons_uniq.
    by move=> p /pairsP[pe _ _]; case/andP: (subdiv_pathP m pe) => /andP[].
  move=> p q pz qz z; have [pe np _] := pairsP p pz; have [qe nq qc] := pairsP q qz.
  rewrite !mem_rcons !inE => /predU1P[->|zp] /predU1P[|zq].
  - by move/subdiv_branch_inj; apply: pinj.
  - by have := subdiv_path_branch p.2 qe zq; rewrite eqxx.
  - by move=> zq; have := subdiv_path_branch q.2 pe zp; rewrite zq eqxx.
  case/doubleton_eq_iff: (subdiv_path_disjoint pe qe zp zq) => -[e1 e2].
    by apply: pinj.
  by have := next_next_neq uc c3 qc; rewrite nq -e1 np e2 eqxx.
have sI : 3 < size I.
  by rewrite size_subdiv_walk size_rcons; apply: leq_trans s4 (leq_addr _ _).
split=> //; split; first by rewrite /seq_cycle /ucycleb uI (ltnW sI) (cycle_path (B x)) lI pI.
move=> u v uI' vI' uv.
have I0 : I != [::] by case: (I) sI.
rewrite (seq_cycle_edge_list_last I0 lI) subdiv_walk_edges.
have revE a b : a -- b -> seq_edge_list (B b :: rcons (P b a) (B a)) =i
                         seq_edge_list (B a :: rcons (P a b) (B b)).
  move=> ab e; rewrite (subdiv_pathC m ab) -rcons_cons -rev_rcons -rev_cons.
  by rewrite seq_edge_list_rev mem_rev.
have out a b z : a -- b -> a \notin c -> z \in B a :: rcons (P a b) (B b) -> z \in I ->
    z = B b.
  move=> ab ac zab /memI[p pz]; have [pe _ _] := pairsP p pz; have [p1c p2c] := pc p pz.
  move: zab; rewrite inE mem_rcons inE mem_rcons inE => /or3P[/eqP->|/eqP-> //|za].
    case/predU1P=> [/subdiv_branch_inj e|zp]; first by rewrite e p2c in ac.
    by have := subdiv_path_branch a pe zp; rewrite eqxx.
  case/predU1P=> [e|zp]; first by have := subdiv_path_branch p.2 ab za; rewrite e eqxx.
  by case/doubleton_eq_iff: (subdiv_path_disjoint ab pe za zp) => -[e _];
    rewrite e ?p1c ?p2c in ac.
have inc a b : a -- b -> [set u; v] \in seq_edge_list (B a :: rcons (P a b) (B b)) -> a \in c.
  move=> ab e; have uw := mem_seq_edge_list e (set21 _ _).
  have vw := mem_seq_edge_list e (set22 _ _); apply: contraTT uv => ac.
  by rewrite (out a b u ab ac uw uI') (out a b v ab ac vw vI') sg_irrefl.
have [a [b [ab ev]]] := spans.2 u v uv.
have ac := inc a b ab ev; have bc : b \in c by apply: (inc b a); [rewrite sg_sym | rewrite revE].
move: (chK a b ac bc ab); rewrite seq_cycle_edge_list_cons => /mapP[p pz eab].
apply/flattenP; exists (seq_edge_list (B p.1 :: rcons (P p.1 p.2) (B p.2))).
  by apply/mapP; exists p.
case/doubleton_eq_iff: eab => -[ea eb]; first by rewrite -ea -eb.
by rewrite -ea -eb -revE // sg_sym.
Qed.

End SubdivisionHoles.

(** ** Induced copies and the induced biclique number *)

(** Having an induced copy of [H] is decidable: an induced copy is a function [H -> G], which can
    be tabulated, satisfying two boolean conditions. *)
Lemma has_induced_copyP (G H : sgraph) :
  reflect (has_induced_copy G H)
    [exists f : {ffun H -> G}, injectiveb f && [forall x, forall y, (f x -- f y) == (x -- y)]].
Proof.
apply: (iffP existsP) => [[f /andP[/injectiveP fi /'forall_'forall_eqP fm]]|[i]].
  exact: inhabits (ISubgraph fi fm).
exists (finfun i); apply/andP; split.
  by apply/injectiveP => x y; rewrite !ffunE => /isubgraph_inj.
by apply/'forall_'forall_eqP => x y; rewrite !ffunE isubgraph_mono.
Qed.

(** [K_n,m] is an induced subgraph of [K_n',m'] for [n <= n'] and [m <= m']. *)
Lemma isubgraph_KB (n m n' m' : nat) : n <= n' -> m <= m' -> 'K_n,m ⇀ 'K_n',m'.
Proof.
move=> nn mm; pose f (u : 'K_n,m) : 'K_n',m' :=
  match u with inl i => inl (widen_ord nn i) | inr i => inr (widen_ord mm i) end.
have fi : injective f by move=> [a|a] [b|b] //= [] /val_inj ->.
by apply: (ISubgraph fi) => -[a|a] [b|b].
Qed.

(** Every graph has an induced biclique number. *)
Lemma induced_biclique_number_exists (G : sgraph) : exists t, induced_biclique_number G t.
Proof.
pose P s := [exists f : {ffun 'K_s,s -> G},
  injectiveb f && [forall x, forall y, (f x -- f y) == (x -- y)]].
have hP s : reflect (has_induced_copy G 'K_s,s) (P s) := has_induced_copyP G 'K_s,s.
have ex : exists s, P s.
  exists 0; apply/hP; have e : 'K_0,0 -> G by case=> -[].
  by constructor; apply: (@ISubgraph _ _ e); case=> -[].
have ub s : P s -> s <= #|G|.
  move=> /hP[i]; have := leq_card i (isubgraph_inj i).
  by rewrite card_sum !card_ord; apply: leq_trans; rewrite leq_addr.
by case: (ex_maxnP ex ub) => t /hP ct maxt; exists t; split=> // s /hP; apply: maxt.
Qed.

(** The tree-independence number is at most [k'] if it is at most [k <= k']. *)
Lemma tree_independence_leW (G : sgraph) (k k' : nat) :
  k <= k' -> tree_independence_le G k -> tree_independence_le G k'.
Proof. by move=> kk [T [D [dec ab]]]; exists T, D; split=> // t; apply: leq_trans (ab t) kk. Qed.

(** The induced matching treewidth is at most [m'] if it is at most [m <= m']. *)
Lemma induced_matching_tw_leW (G : sgraph) (m m' : nat) :
  m <= m' -> induced_matching_tw_le G m -> induced_matching_tw_le G m'.
Proof.
move=> mm [T [D [dec bnd]]]; exists T, D; split=> // M im cov.
exact: leq_trans (bnd M im cov) mm.
Qed.

(** ** Decidability of minors; Hadwiger number and fractional Hadwiger number *)

(** Boolean version of [minor]: some map from the vertices of [H] to the sets of vertices of [G]
    is a model of [H] in [G] ([minor_rmap] of GraphTheory). *)
Definition minorb (G H : sgraph) : bool :=
  [exists phi : {ffun H -> {set G}},
    [&& [forall x, phi x != set0], [forall x, connectedb (phi x)],
        [forall x, forall y, (x != y) ==> [disjoint phi x & phi y]] &
        [forall x, forall y, (x -- y) ==> neighbor (phi x) (phi y)]]].

Lemma minorP (G H : sgraph) : reflect (minor G H) (minorb G H).
Proof.
apply: (iffP existsP) => [[phi /and4P[/forallP p1 /forallP p2 /forallP p3 /forallP p4]]|].
  apply: (@minor_of_rmap _ _ phi); split => // [x|x y|x y]; first exact/connectedP.
    by move/forallP: (p3 x) => /(_ y) /implyP.
  by move/forallP: (p4 x) => /(_ y) /implyP.
case/minorRE => phi [q1 q2 q3 q4]; exists (finfun phi).
apply/and4P; split; apply/forallP => x; rewrite ?ffunE //; first exact/connectedP.
  by apply/forallP => y; rewrite !ffunE; apply/implyP; apply: q3.
by apply/forallP => y; rewrite !ffunE; apply/implyP; apply: q4.
Qed.

(** A graph with a [K_n] minor has a [K_m] minor for every [m <= n]. *)
Lemma minor_K_le (G : sgraph) (m n : nat) : m <= n -> minor G 'K_n -> minor G 'K_m.
Proof.
move=> mn /minor_trans; apply; apply: (@minor_of_clique _ [set: 'K_n]); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

(** Every graph has a Hadwiger number. *)
Lemma hadwiger_number_exists (G : sgraph) : exists h, hadwiger_number G h.
Proof.
have ex : exists k, minorb G 'K_k.
  by exists 0; apply/minorP; apply: (@minor_of_clique _ set0) => // x; rewrite inE.
have bd k : minorb G 'K_k -> k <= #|G|.
  by case: k => // k /minorP m; rewrite ltnNge; apply/negP => /small_K_free.
by case: (ex_maxnP ex bd) => h /minorP hm hmax; exists h; split => // h' /minorP /hmax.
Qed.

