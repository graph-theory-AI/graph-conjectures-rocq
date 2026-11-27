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

(** ** Forests *)

Section PathGraph.
Variable n : nat.
Implicit Types (x z : path_graph n) (s : seq (path_graph n)).

Lemma path_graph_edge x z : x -- z = ((val x).+1 == val z) || ((val z).+1 == val x).
Proof.
rewrite /edge_rel /= /sc; case: eqP => [->|_] //.
by rewrite (gtn_eqF (ltnSn _)).
Qed.

(** A walk in the path takes every value between its first and last vertices. *)
Lemma path_graph_ivt z s v :
  path (--) z s -> val z <= v <= val (last z s) -> exists2 w, w \in z :: s & val w = v.
Proof.
elim: s z => [|a s IH] z /=.
  by move=> _ /andP[zv vz]; exists z; rewrite ?mem_head //; apply/eqP; rewrite eqn_leq zv vz.
case/andP=> za pth /andP[zv vl]; have [<-|zv'] := eqVneq (val z) v.
  by exists z; rewrite ?mem_head.
have [|w ws <-] := IH a pth; last by exists w; rewrite // inE ws orbT.
rewrite vl andbT; move: za; rewrite path_graph_edge => /orP[]/eqP ez.
  by rewrite -ez ltn_neqAle zv' zv.
by rewrite -ltnS ez ltnW.
Qed.

(** A path in the path that ends above its first vertex goes up at each step. *)
Lemma path_graph_up x s :
  path (--) x s -> uniq (x :: s) -> val x <= val (last x s) ->
  map val s = iota (val x).+1 (val (last x s) - val x).
Proof.
elim: s x => [|z s IH] x; first by rewrite /= subnn.
case/andP=> xz pth; rewrite cons_uniq => /andP[xs us] xl.
have {}xl : val x < val (last z s).
  rewrite ltn_neqAle xl andbT; apply: contra xs => /eqP/val_inj ->; exact: mem_last.
move: xz; rewrite path_graph_edge => /orP[]/eqP ez.
  by rewrite [last _ _]/= -(subnSK xl) ez map_cons (IH z) // -ez.
have [|w ws /val_inj wx] := @path_graph_ivt z s (val x) pth.
  by rewrite (ltnW xl) -ez leqnSn.
by rewrite -wx ws in xs.
Qed.

(** The path is a forest. *)
Lemma path_graph_forest : is_forest [set: path_graph n].
Proof.
apply: unique_forestT => x y.
wlog xy : x y / val x <= val y => [W|p q Ip Iq].
  have [/W //|/ltnW yx p q Ip Iq] := leqP (val x) (val y).
  by apply: prev_inj; apply: W; rewrite ?irred_rev.
apply/eqP; rewrite -nodes_eqE !nodesE eqseq_cons eqxx /=; apply/eqP/(inj_map val_inj).
move: Ip Iq; rewrite !irredE !nodesE => Ip Iq.
by rewrite !(path_graph_up (pathpW (valP _))) ?path_last.
Qed.

End PathGraph.

Section ForestPaths.
Variables (T : sgraph) (x0 : T).
Hypothesis forestT : is_forest [set: T].

(** In a forest, the first vertex of a path is adjacent to no other vertex of the path than the
    second. *)
Lemma forest_path_head x s k :
  path (--) x s -> uniq (x :: s) -> 0 < k < size s -> ~~ (x -- nth x0 s k).
Proof.
move=> pth uq /andP[k0 ks]; have sk : size (take k.+1 s) = k.+1 by rewrite size_takel.
have -> : nth x0 s k = last x (take k.+1 s).
  by rewrite -nth_last sk nth_take // (set_nth_default x0).
have pk : path (--) x (take k.+1 s).
  by move: pth; rewrite -[s in path _ _ s](cat_take_drop k.+1) cat_path => /andP[].
apply/negP => xy.
have irr : irred (Path_of_path pk).
  by rewrite irredE nodesE; apply: subseq_uniq uq; rewrite /= eqxx take_subseq.
have /(congr1 (size \o val)) := forestT_unique forestT irr (irred_edge xy).
by rewrite /= sk => -[k0']; rewrite k0' in k0.
Qed.

(** The paths of a forest are induced paths: no two non-consecutive vertices of a path are
    adjacent. *)
Lemma forest_path_nonadj x s i j :
  path (--) x s -> uniq (x :: s) -> j < size (x :: s) -> i.+1 < j ->
  ~~ (nth x0 (x :: s) i -- nth x0 (x :: s) j).
Proof.
elim: s x i j => [|z s IH] x i j pth uq; first by case: j => [|[]].
case: i j => [|i] [|j] // js ij; first by apply: (forest_path_head pth uq); apply/andP.
by case/andP: pth => _ /IH; apply => //; case/andP: uq.
Qed.

End ForestPaths.

(** A graph in which all edges contain a vertex [c] is a forest: its paths have at most three
    vertices, and the middle one of a path with three vertices is [c]. *)
Lemma center_forest (G : sgraph) (c : G) :
  (forall u v : G, u -- v -> (u == c) || (v == c)) -> is_forest [set: G].
Proof.
move=> cE; apply: unique_forestT => x y p q Ip Iq.
suff nE (r : Path x y) : irred r ->
    nodes r = if x == y then [:: x] else if x -- y then [:: x; y] else [:: x; c; y].
  by apply/eqP; rewrite -nodes_eqE (nE p) // (nE q).
rewrite irredE nodesE; case: r => -[|a [|b [|d s]]] /= /andP[pth /eqP <-] //=.
- by rewrite eqxx.
- by case/andP: pth => -> _; rewrite inE andbT => /negbTE ->.
- move: pth => /= /andP[xa /andP[ab _]]; rewrite !inE !negb_or !andbT.
  case/andP => /andP[xa' /negbTE xb] ab'; rewrite xb.
  have /orP[/eqP xc|/eqP ac] := cE _ _ xa.
    by have := cE _ _ ab; rewrite -xc !(eq_sym _ x) (negbTE xa') xb.
  rewrite -ac; have [/cE|//] := ifPn.
  by rewrite -ac (negbTE xa') eq_sym (negbTE ab').
- case/and5P; rewrite !inE !negb_or => /and4P[_ xb xd _] /and3P[ab ad _] _ _ _.
  move: pth => /= /and4P[xa _ bd _].
  have := cE _ _ xa; have := cE _ _ bd => /orP[]/eqP e1 /orP[]/eqP e2.
  all: by move: xb xd ab ad; rewrite e1 e2 eqxx.
Qed.

(** The star ['K_1,a] is a forest. *)
Lemma star_forest (a : nat) : is_forest [set: 'K_1,a].
Proof.
apply: (@center_forest 'K_1,a (inl ord0)) => -[i|i] [j|j] // _.
  by rewrite (ord1 i) eqxx.
by rewrite (ord1 j) eqxx orbT.
Qed.

(** ** Edge-connectivity and minimum degree *)

(** Whitney's inequality: a [k]-edge-connected graph with at least two vertices has minimum degree
    at least [k] (consider the cut of a single vertex). *)
Lemma edge_connected_min_degree (G : sgraph) (k : nat) :
  1 < #|G| -> edge_connected G k -> min_degree_ge G k.
Proof.
move=> G1 conn v; apply: leq_trans (conn [set v] _ _) _.
- by apply/set0Pn; exists v; rewrite inE.
- by apply: contraTneq G1 => vT; rewrite -cardsT -vT cards1.
apply: leq_trans (leq_imset_card (fun w => [set v; w]) N(v)).
apply/subset_leq_card/subsetP => e; rewrite inE => /andP[/edgesP[x [y [-> xy]]]].
case/andP => /set0Pn[a /setIP[+ /set1P av]] _; rewrite av.
by case/set2P => ->; [|rewrite setUC]; apply: imset_f; rewrite in_opn // sg_sym.
Qed.

(** ** Leaves of forests *)

Section ForestLeaves.
Variable G : sgraph.
Hypothesis forestG : is_forest [set: G].

(** [branch v u w]: [w] is joined to [u] in [G - v]. *)
Local Abbreviation branch v := (connect (restrict (~: [set v]) (--))).

(** If [v -- u], the branch at [v] containing [u] contains a leaf: the end of a longest path that
    starts with the edge [vu] has no other neighbour than its predecessor. *)
Lemma forest_branch_leaf (v u : G) : v -- u -> exists2 w : G, #|N(w)| == 1 & branch v u w.
Proof.
move=> vu; pose P n := [exists s : n.-tuple G, path (--) v (u :: s) && uniq (v :: u :: s)].
have P0 : P 0 by apply/existsP; exists [tuple]; rewrite /= vu inE sg_edgeNeq.
have Pmax n : P n -> n <= #|G|.
  case/existsP => s /andP[_ /card_uniqP sz]; apply: leq_trans (max_card (mem (v :: u :: s))).
  by rewrite sz /= size_tuple leqW.
case: (@ex_maxnP P #|G| (ex_intro _ 0 P0) Pmax) => n /existsP[s /andP[pth uq]] maxn.
set w := last u s; exists w; last first.
  apply/connectP; exists (val s) => //; move: pth uq => /= /andP[_] /path_rpath + /andP[vs _].
  by apply=> [|a aS]; rewrite !inE; apply: contraNneq vs => <-; rewrite ?inE ?eqxx ?aS ?orbT.
set r := srev v (u :: s).
have pr : path (--) w r by move: pth; rewrite path_srev.
have revr : rev (v :: u :: s) = w :: r by rewrite lastI rev_rcons.
have ur : uniq (w :: r) by rewrite -revr rev_uniq.
suff Nw : N(w) = [set nth w r 0] by rewrite Nw cards1.
apply/eqP; rewrite eq_sym eqEsubset sub1set in_opn; apply/andP; split.
  have : 0 < size r by rewrite size_rev size_belast.
  by case: r pr {revr ur} => //= y r' /andP[].
apply/subsetP => z; rewrite in_opn inE => wz.
have [zr|zr] := boolP (z \in w :: r); last first.
  have /maxn : P n.+1; last by rewrite ltnn.
  apply/existsP; exists [tuple of rcons s z].
  change (path (--) v (rcons (u :: s) z) && uniq (rcons (v :: u :: s) z)).
  by rewrite rcons_path rcons_uniq pth uq andbT -mem_rev revr zr andbT; apply: wz.
have := zr; rewrite -index_mem; move: wz.
rewrite -[z in _ -- z](nth_index w zr) -[z in z == _](nth_index w zr).
case: (index z (w :: r)) => [|[|k]] /=; [by rewrite sg_irrefl|by rewrite eqxx|].
by move=> wk kr; have /(_ kr) := forest_path_head w forestG pr ur (k := k.+1); rewrite wk.
Qed.

(** Distinct neighbours of [v] lie in distinct branches at [v], as the path from [v] to any vertex
    is unique. *)
Lemma forest_branch_uniq (v u u' w : G) :
  v -- u -> v -- u' -> branch v u w -> branch v u' w -> u = u'.
Proof.
suff irr (a : G) : v -- a -> branch v a w -> exists2 p : Path v w, irred p & head v (val p) = a.
  move=> /irr + /irr => H H' /H[p Ip <-] /H'[q Iq <-].
  by rewrite (forestT_unique forestG Ip Iq).
move=> va; have [<- _|aw] := eqVneq a w; first by exists (edgep va); rewrite ?irred_edge.
case/connect_irredRP => // p Ip /subsetP sub; exists (pcat (edgep va) p) => //.
by rewrite irred_edgeL Ip andbT; apply/negP => /sub; rewrite !inE eqxx.
Qed.

(** A forest has at least as many leaves as its maximum degree. *)
Lemma forest_Delta_le_leaves : Delta G <= #|[set v : G | #|N(v)| == 1]|.
Proof.
apply/bigmax_leqP => v _; pose br w := odflt v [pick u | v -- u & branch v u w].
apply: leq_trans (leq_imset_card br _); apply/subset_leq_card/subsetP => u.
rewrite in_opn => vu; have [w lw uw] := forest_branch_leaf vu.
apply/imsetP; exists w; rewrite ?inE // /br; case: pickP => [u' /andP[vu' u'w]|/(_ u)].
  exact: forest_branch_uniq vu vu' uw u'w.
by rewrite vu uw.
Qed.

End ForestLeaves.

(** ** Girth *)

(** A graph of girth at least 4 is triangle-free. *)
Lemma girth_ge4_triangle_free (G : sgraph) : girth_ge G 4 -> triangle_free G.
Proof.
move=> g4 x y z xy yz zx; have xz : x -- z by rewrite sg_sym.
suff /g4 : seq_cycle (--) [:: x; y; z] by [].
by rewrite /seq_cycle /ucycleb /= xy yz zx !inE !negb_or !sg_edgeNeq.
Qed.

(** ** Minimum degree two *)

(** A nonempty set of vertices in which every vertex has at least two neighbours contains the
    vertices of a cycle: the neighbours of the first vertex of a longest path in the set lie on
    the path, and one of them is not the second vertex. *)
Lemma min_degree2_seq_cycle (G : sgraph) (S : {set G}) :
  S != set0 -> (forall x, x \in S -> 1 < #|N(x) :&: S|) ->
  exists c : seq G, seq_cycle (--) c /\ {subset c <= S}.
Proof.
move=> /set0Pn[x xS] degS.
suff ext n w s : #|G| <= size s + n -> path (--) w s -> uniq (w :: s) ->
    {subset w :: s <= S} -> exists c : seq G, seq_cycle (--) c /\ {subset c <= S}.
  by apply: (ext #|G| x [::]) => // z; rewrite inE => /eqP->.
elim: n w s => [|n IH] w s sz pth uq sS.
  by rewrite addn0 in sz; have := max_card (mem (w :: s)); rewrite (card_uniqP uq) ltnNge sz.
have wS : w \in S by apply: sS; rewrite inE eqxx.
have [/exists_inP[z zN zs]|/exists_inPn Ns] := boolP [exists z in N(w) :&: S, z \notin s].
  have zw : z != w by apply: contraTneq zN => ->; rewrite inE in_opn sg_irrefl.
  apply: (IH z (w :: s)); first by rewrite /= addSnnS.
  - by move: zN; rewrite /= pth andbT inE in_opn sg_sym => /andP[].
  - by rewrite /= inE negb_or zw zs.
  by move=> y; rewrite inE => /predU1P[->|]; [case/setIP: zN|apply: sS].
have [y yN ya] : exists2 y, y \in N(w) :&: S & y != nth w s 0.
  have /card_gt1P[a [b [aN bN ab]]] := degS w wS.
  by have [ea|] := eqVneq a (nth w s 0); [exists b; rewrite // -ea eq_sym|exists a].
have ys := negbNE (Ns _ yN); set i := index y s; have ilt : i < size s by rewrite index_mem.
have i0 : 0 < i by rewrite lt0n; apply: contra ya => /eqP i0; rewrite -i0 nth_index.
have tk : take i.+1 s = rcons (take i s) y by rewrite -(nth_index w ys) -take_nth.
have sub : subseq (w :: take i.+1 s) (w :: s) by rewrite /= eqxx take_subseq.
exists (w :: take i.+1 s); split; last by move=> z /(mem_subseq sub)/sS.
rewrite /seq_cycle /ucycleb (subseq_uniq sub uq) /= (size_takel ilt) !ltnS i0 !andbT.
rewrite rcons_path {2}tk last_rcons; apply/andP; split.
  by move: pth; rewrite -[s in path _ _ s](cat_take_drop i.+1) cat_path => /andP[].
by case/setIP: yN; rewrite in_opn sg_sym.
Qed.
