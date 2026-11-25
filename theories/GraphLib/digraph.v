(** * Digraphs

Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
edge relation [--].  Digons and loops are allowed, parallel edges are not represented.
Edges are called arcs here.

Classes of digraphs are predicates on [D : diGraph]: [irreflexive (@edge_rel D)] (no loop),
[oriented D] (no loop, no digon), [tournament D].  The following notions are those of
GraphTheory: [N(v)] (out-neighbourhood), [num_edges D], [induced A] (induced subdigraph, with
[induced [set~ v]] for the deletion of [v]), [is_dhom f] (homomorphism), [D1 ≃ D2]
(isomorphism) and [H ⇀ D] (induced copy of [H] in [D]), the latter two being types, hence
[inhabited (D1 ≃ D2)] and [inhabited (H ⇀ D)] in propositions. *)

(* [digraph] comes last: [induced] and [induced_rel] are those of digraphs, not of sgraphs *)
From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot order perm algebra.
From GC.GraphLib Require Import misc homomorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** * Definitions *)

(** ** Classes of digraphs *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] is a transitive tournament. *)
Definition is_transitive_tournament (D : diGraph) : Prop :=
  tournament D /\ transitive (@edge_rel D).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** ** Underlying graph *)

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** [D] is an orientation of a tree (with at least one vertex). *)
Definition oriented_tree (D : diGraph) : Prop :=
  [/\ (0 < #|D|)%N, oriented D & is_tree [set: underlying D]].

(** [D] is an orientation of a star. *)
Definition oriented_star (D : diGraph) : Prop :=
  oriented D /\
  exists c : underlying D,
    (forall v : underlying D, v != c -> c -- v) /\
    (forall u v : underlying D, u != c -> v != c -> u != v -> ~~ (u -- v)).

(** [D] is an orientation of the path with [k] edges. *)
Definition oriented_path (D : diGraph) (k : nat) : Prop :=
  oriented D /\ inhabited (underlying D ≃ path_graph k.+1).

(** ** Neighbourhoods and degrees *)

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Second out-neighbourhood: the vertices at distance exactly two from [v]. *)
Definition second_outneigh (D : diGraph) (v : D) : {set D} :=
  NS(N(v)) :\: N[v].

(** The minimum out-degree of [D] is at least [k]. *)
Definition min_outdeg_ge (D : diGraph) (k : nat) : Prop := forall v : D, (k <= outdeg v)%N.

(** The minimum in-degree and the minimum out-degree of [D] are at least [k]. *)
Definition min_semidegree_ge (D : diGraph) (k : nat) : Prop :=
  forall v : D, (k <= outdeg v)%N /\ (k <= indeg v)%N.

(** [D] is [d]-diregular: all in-degrees and out-degrees are equal to [d]. *)
Definition diregular (D : diGraph) (d : nat) : bool :=
  [forall v : D, (outdeg v == d) && (indeg v == d)].

(** Each vertex has as many in-neighbours as out-neighbours (such a digraph is also called
    eulerian, connected or not). *)
Definition balanced_digraph (D : diGraph) : bool := [forall v : D, indeg v == outdeg v].

(** Each vertex is a source or a sink. *)
Definition antidirected (D : diGraph) : Prop := forall v : D, indeg v = 0 \/ outdeg v = 0.

(** ** Arcs *)

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** The arcs from [B] to its complement. *)
Definition outcut (D : diGraph) (B : {set D}) : {set D * D} :=
  [set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 -- p.2]].

(** Maximum average degree: the maximum of 2|A(S)|/|S| over nonempty [S] (0 if [D] is empty). *)
Definition digraph_mad (D : diGraph) : rat :=
  (\big[Num.max/0]_(S in [set S : {set D} | S != set0])
     ((2 * num_edges (induced S))%:Q / (#|S|)%:Q))%R.

(** ** Operations *)

(** Reversal of all arcs. *)
Definition converse (D : diGraph) : diGraph := DiGraph [rel u v : D | v -- u].

(** Deletion of the arcs of [F]. *)
Definition del_arcs (D : diGraph) (F : {set D * D}) : diGraph :=
  DiGraph (fun u v : D => (u -- v) && ((u, v) \notin F)).

(** Reversal of the arc [a]. *)
Definition reverse_arc (D : diGraph) (a : D * D) : diGraph :=
  DiGraph (fun u v : D => if (u == a.1) && (v == a.2) then false
                          else if (u == a.2) && (v == a.1) then true else u -- v).

(** Switching: reversal of the arcs with exactly one end in [S]. *)
Definition digraph_switch (D : diGraph) (S : {set D}) : diGraph :=
  DiGraph (fun u v : D => if (u \in S) (+) (v \in S) then v -- u else u -- v).

(** Disjoint union. *)
Definition digraph_sum (D1 D2 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end).

(** D1 => D2: disjoint union, plus all the arcs from [D1] to [D2]. *)
Definition digraph_join (D1 D2 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | inl _, inr _ => true
    | inr _, inl _ => false
    end).

(** Δ(D1,D2,D3): substitution of [D1], [D2], [D3] in the three vertices of a directed triangle
    (all the arcs from [D1] to [D2], from [D2] to [D3] and from [D3] to [D1]). *)
Definition c3_subst (D1 D2 D3 : diGraph) : diGraph :=
  DiGraph (fun x y : D1 + D2 + D3 =>
    match x, y with
    | inl (inl a), inl (inl a') => a -- a'
    | inl (inr b), inl (inr b') => b -- b'
    | inr c, inr c' => c -- c'
    | inl (inl _), inl (inr _) => true
    | inl (inr _), inr _ => true
    | inr _, inl (inl _) => true
    | _, _ => false
    end).

(** Δ(1,2,2): the vertices of a directed triangle are replaced by one vertex, one arc, one arc. *)
Definition delta_1_2_2 : diGraph :=
  c3_subst (transitive_tournament 1) (transitive_tournament 2) (transitive_tournament 2).

(** Substitution of [D2] for the vertex [u] of [D1]. *)
Definition digraph_subst (D1 : diGraph) (u : D1) (D2 : diGraph) : diGraph :=
  DiGraph (fun a b : {x : D1 | x != u} + D2 =>
    match a, b with
    | inl x, inl y => val x -- val y
    | inr x, inr y => x -- y
    | inl x, inr _ => val x -- u
    | inr _, inl y => u -- val y
    end).

(** Blow-up: each vertex is replaced by [k] copies without arcs between them. *)
Definition digraph_blowup (D : diGraph) (k : nat) : diGraph :=
  DiGraph (fun a b : D * 'I_k => a.1 -- b.1).

(** ** Directed paths and cycles *)

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The arcs of the directed path [x :: s]. *)
Definition dipath_arcs (D : diGraph) (x : D) (s : seq D) : {set D * D} :=
  [set p in zip (x :: s) s].

(** The arcs of the directed cycle [c]. *)
Definition dicycle_arcs (D : diGraph) (c : seq D) : {set D * D} :=
  [set p : D * D | (p.1 \in c) && (next c p.1 == p.2)].

(** [D] has a directed path of length [k]. *)
Definition has_dipath (D : diGraph) (k : nat) : bool :=
  [exists x : D, exists t : k.-tuple D, dipath x t].

(** The maximum length of a directed path of [D] (0 if [D] is empty). *)
Definition longest_dipath_length (D : diGraph) : nat :=
  \max_(k < #|D| | has_dipath D k) (k : nat).

(** [c] is a directed cycle of maximum length. *)
Definition longest_dicycle (D : diGraph) (c : seq D) : Prop :=
  dicycle c /\ forall d : seq D, dicycle d -> (size d <= size c)%N.

(** [c] is a Hamiltonian directed cycle. *)
Definition hamiltonian_dicycle (D : diGraph) (c : seq D) : bool := dicycle c && (size c == #|D|).

(** The directed cycle [c] is induced: the arcs between its vertices are those of [c]. *)
Definition induced_dicycle (D : diGraph) (c : seq D) : Prop :=
  dicycle c /\ {in c &, forall u v : D, u -- v -> next c u = v}.

(** The number of directed cycles of [D], given by their sets of arcs (they have at most [#|D|]
    vertices). *)
Definition dicycle_count (D : diGraph) : nat :=
  #|[set A : {set D * D} | [exists k : 'I_#|D|.+1, exists c : k.-tuple D,
       dicycle c && (A == dicycle_arcs c)]]|.

(** The directed girth of [D] is larger than [r]. *)
Definition digirth_gt (D : diGraph) (r : nat) : Prop :=
  forall c : seq D, dicycle c -> (r < size c)%N.

(** [Q] is a partition of the vertices into directed paths ([(x, s)] stands for [x :: s]). *)
Definition dipath_partition (D : diGraph) (Q : seq (D * seq D)) : bool :=
  [&& all (fun p => dipath p.1 p.2) Q,
      [forall v : D, has (fun p => v \in p.1 :: p.2) Q] &
      [forall v : D, count (fun p => v \in p.1 :: p.2) Q <= 1]].

(** The [k]-norm of a family of paths: the sum of min(k, number of vertices). *)
Definition dipath_knorm (D : diGraph) (k : nat) (Q : seq (D * seq D)) : nat :=
  \sum_(p <- Q) minn k (size (p.1 :: p.2)).

(** ** Strong connectivity *)

(** [D] is strongly connected. *)
Definition strongly_connected (D : diGraph) : bool :=
  [forall x : D, forall y : D, connect (--) x y].

(** [D] is [k]-strong: it has more than [k] vertices, and it remains strongly connected when
    fewer than [k] vertices are deleted. *)
Definition kstrong (D : diGraph) (k : nat) : bool :=
  (k < #|D|) && [forall S : {set D}, (#|S| < k) ==> strongly_connected (induced (~: S))].

(** [D] is [k]-arc-strong: at least [k] arcs leave each nonempty proper set of vertices (always
    true if [D] has at most one vertex). *)
Definition arc_strong (D : diGraph) (k : nat) : bool :=
  [forall B : {set D}, ((B != set0) && (B != [set: D])) ==> (k <= #|outcut B|)].

(** The arcs of [A] form a strongly connected spanning subdigraph of [D]. *)
Definition spanning_strong (D : diGraph) (A : {set D * D}) : Prop :=
  A \subset arcs D /\ strongly_connected (digraph_of_arcs A).

(** Strong arc decomposition: the arcs of [D] can be partitioned into two strongly connected
    spanning subdigraphs. *)
Definition strong_arc_decomposition (D : diGraph) : Prop :=
  exists A1 A2 : {set D * D},
    [/\ [disjoint A1 & A2], A1 :|: A2 = arcs D, spanning_strong A1 & spanning_strong A2].

(** [B] is the source side of a dicut: it is nonempty and proper, and no arc enters it
    (the dicut is then [outcut B]). *)
Definition dicut_side (D : diGraph) (B : {set D}) : bool :=
  [&& B != set0, B != [set: D] & outcut (~: B) == set0].

(** The arc set [F] is a dijoin: it meets all the dicuts of [D]. *)
Definition dijoin (D : diGraph) (F : {set D * D}) : bool :=
  (F \subset arcs D) && [forall B : {set D}, dicut_side B ==> ~~ [disjoint F & outcut B]].

(** ** Acyclic digraphs, dichromatic number *)

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** The fractional dichromatic number of [D] is at most [p]: nonnegative weights on the
    sets inducing an acyclic digraph, of total at most [p], cover each vertex with weight
    at least 1.  Weights are taken in an ordered field [R]. *)
Definition fractional_dicolorable (R : realFieldType) (D : diGraph) (p : R) : Prop :=
  (exists x : {set D} -> R,
    [/\ forall A : {set D}, 0 <= x A,
        forall v : D, 1 <= \sum_(A : {set D} | acyclic (induced A) && (v \in A)) x A
      & \sum_(A : {set D} | acyclic (induced A)) x A <= p])%R.

(** [F] is the arc set of a spanning out-branching rooted at [r]. *)
Definition out_branching (D : diGraph) (F : {set D * D}) (r : D) : bool :=
  let B := digraph_of_arcs F in
  [&& F \subset arcs D, @indeg B r == 0,
      [forall v : D, (v != r) ==> (@indeg B v == 1)] & acyclic B].

(** [F] is the arc set of a spanning in-branching rooted at [r]. *)
Definition in_branching (D : diGraph) (F : {set D * D}) (r : D) : bool :=
  let B := digraph_of_arcs F in
  [&& F \subset arcs D, @outdeg B r == 0,
      [forall v : D, (v != r) ==> (@outdeg B v == 1)] & acyclic B].

(** The minimum size of a set of arcs that meets all directed cycles. *)
Definition feedback_arc_number (D : diGraph) : nat :=
  #|[arg min_(F < [set: D * D] | acyclic (del_arcs F)) #|F|]|.

(** The maximum size of a set inducing an acyclic digraph. *)
Definition acyclic_number (D : diGraph) : nat :=
  \max_(S : {set D} | acyclic (induced S)) #|S|.

(** The dichromatic number, i.e., the least [k] such that the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dichromatic_number (D : diGraph) : nat :=
  \big[minn/#|D|]_(k < #|D|.+1 |
     [exists col : {ffun D -> 'I_k}, [forall i : 'I_k, acyclic (induced [set v | col v == i])]])
     (k : nat).

(** The digraphs of the class [C] have a bounded dichromatic number. *)
Definition dichromatic_bounded (C : diGraph -> Prop) : Prop :=
  exists B : nat, forall D : diGraph, C D -> dicolorable D B.

(** ** Subdigraphs and subdivisions *)

(** [D] contains a (not necessarily induced) copy of [H]. *)
Definition subdigraph (H D : diGraph) : Prop :=
  exists f : H -> D, injective f /\ forall u v : H, u -- v -> f u -- f v.

(** [D] contains a subdivision of [F]: distinct branch vertices, and, for each arc of [F], a
    directed path between the corresponding branch vertices; the interiors of these paths are
    pairwise disjoint and contain no branch vertex. *)
Definition contains_disubdivision (F D : diGraph) : Prop :=
  exists branch : F -> D,
    injective branch /\
    exists paths : F -> F -> seq D,
      (forall u v : F, u -- v ->
        [/\ (0 < size (paths u v))%N,
            upath (branch u) (branch v) (paths u v)
          & [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
             & [set y | [exists x : F, branch x == y]]]]) /\
      (forall u v x y : F, u -- v -> x -- y ->
        ((u != x) || (v != y)) ->
        [disjoint seq_interior (branch u) (branch v) (branch u :: paths u v)
         & seq_interior (branch x) (branch y) (branch x :: paths x y)]).

(** [F] is δ⁺-maderian: the digraphs of large minimum out-degree contain a subdivision of [F]. *)
Definition delta_plus_maderian (F : diGraph) : Prop :=
  exists m : nat, forall D : diGraph, (0 < #|D|)%N ->
    min_outdeg_ge D m -> contains_disubdivision F D.

(** [F] is avoidable: for some function [d], each loopless digraph of minimum out-degree at least
    [d k] contains a digraph of minimum out-degree at least [k] that contains no copy of [F]. *)
Definition avoidable (F : diGraph) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraph),
      irreflexive (@edge_rel D) -> 0 < #|D| -> min_outdeg_ge D (d k) ->
      exists H : diGraph,
        [/\ 0 < #|H|, subdigraph H D, min_outdeg_ge H k & ~ subdigraph F H].

(** ** Colourings *)

(** [D] has an oriented [k]-colouring: a homomorphism to a tournament on [k] vertices. *)
Definition oriented_colorable (D : diGraph) (k : nat) : Prop :=
  exists T : diGraph, [/\ tournament T, #|T| = k & homs_to D T].

(** The out-neighbours of [v] with the colour of [v]. *)
Definition same_color_outneigh (D : diGraph) (C : eqType) (col : D -> C) (v : D) : {set D} :=
  [set w in N(v) | col w == col v].

(** [1/k]-majority colouring: each vertex has the colour of at most [1/k] of its
    out-neighbours.  The majority colourings are those with [k = 2]. *)
Definition majority_coloring (D : diGraph) (C : eqType) (k : nat) (col : D -> C) : bool :=
  [forall v : D, k * #|same_color_outneigh col v| <= outdeg v].

(** [D] is majority [c]-choosable: it has a majority colouring from all lists of size at least
    [c]. *)
Definition majority_choosable (D : diGraph) (c : nat) : Prop :=
  forall (C : finType) (L : D -> {set C}),
    (forall v : D, c <= #|L v|) ->
    exists col : D -> C, (forall v : D, col v \in L v) /\ majority_coloring 2 col.

(** There is a monochromatic directed path from [v] to [w], for the arc-colouring [c]
    ([c] matters only on arcs). *)
Definition mono_reach (D : diGraph) (C : finType) (c : D -> D -> C) (v w : D) : bool :=
  [exists i : C, connect (fun x y : D => (x -- y) && (c x y == i)) v w].

(** ** Independence and domination *)

(** There is no arc inside [S]. *)
Definition arc_free (D : diGraph) (S : {set D}) : bool :=
  [forall u in S, [forall v in S, ~~ (u -- v)]].

(** Independence number. *)
Definition digraph_alpha (D : diGraph) : nat := \max_(S : {set D} | arc_free S) #|S|.

(** [X] dominates [D]: each vertex is in [X] or has an in-neighbour in [X]. *)
Definition out_dominating (D : diGraph) (X : {set D}) : bool :=
  [forall v : D, v \in NS[X]].

(** Domination number. *)
Definition out_domination_number (D : diGraph) : nat :=
  #|[arg min_(X < [set: D] | out_dominating X) #|X|]|.

(** Quasi-kernel, or 2-kernel: an independent set from which each vertex is reached by a directed
    path of length at most 2. *)
Definition quasi_kernel (D : diGraph) (K : {set D}) : Prop :=
  arc_free K /\ forall v : D, v \in NS[NS[K]].

(** ** Automorphisms *)

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** [D] is vertex-transitive. *)
Definition vertex_transitive (D : diGraph) : bool :=
  [forall u : D, [forall v : D, [exists p : {perm D}, (p \in automorphisms D) && (p u == v)]]].

(** ** Vertex orderings, backedge graphs, clique number

A linear order on the vertices is given by a permutation, composed with the canonical
enumeration. *)

(** [u] is before [v] in the order given by [p]. *)
Definition perm_lt (V : finType) (p : {perm V}) (u v : V) : bool :=
  enum_rank (p u) < enum_rank (p v).

Lemma perm_lt_irrefl (V : finType) (p : {perm V}) : irreflexive (perm_lt p).
Proof. by move=> u; rewrite /perm_lt ltnn. Qed.

(** There is an arc between [u] and [v] that goes backward in the order given by [p]. *)
Definition backedge_rel (D : diGraph) (p : {perm D}) : rel D :=
  [rel u v | perm_lt p u v && (v -- u) || perm_lt p v u && (u -- v)].

Lemma backedge_sym (D : diGraph) (p : {perm D}) : symmetric (backedge_rel p).
Proof. by move=> u v; rewrite /backedge_rel /= orbC. Qed.

Lemma backedge_irrefl (D : diGraph) (p : {perm D}) : irreflexive (backedge_rel p).
Proof. by move=> u; rewrite /backedge_rel /= perm_lt_irrefl. Qed.

(** The backedge graph of [D] in the order given by [p]. *)
Definition backedge_graph (D : diGraph) (p : {perm D}) : sgraph :=
  SGraph (backedge_sym p) (backedge_irrefl p).

(** The clique number of the digraph [D]: the minimum clique number of a backedge graph. *)
Definition diclique_number (D : diGraph) : nat :=
  ω([set: backedge_graph [arg min_(p < (1%g : {perm D})) ω([set: backedge_graph p])]]).

(** The dichromatic number is bounded by a function of the clique number in the class [C]. *)
Definition dichi_bounded (C : diGraph -> Prop) : Prop :=
  exists f : nat -> nat, forall D : diGraph, C D ->
    (dichromatic_number D <= f (diclique_number D))%N.

(** The dichromatic number is bounded by a polynomial in the clique number in the class [C]. *)
Definition poly_dichi_bounded (C : diGraph -> Prop) : Prop :=
  exists c d : nat, forall D : diGraph, C D ->
    (dichromatic_number D <= c * diclique_number D ^ d)%N.

(** ** Classes of digraphs (sets of digraphs) *)

(** The class [C] is closed under induced subdigraphs. *)
Definition digraph_induced_closed (C : diGraph -> Prop) : Prop :=
  forall (D : diGraph) (S : {set D}), C D -> C (induced S).

(** The closure of the class [C] under substitution. *)
Inductive subst_closure (C : diGraph -> Prop) : diGraph -> Prop :=
| subst_closure_base (D : diGraph) : C D -> subst_closure C D
| subst_closure_step (D1 : diGraph) (u : D1) (D2 : diGraph) :
    subst_closure C D1 -> subst_closure C D2 -> subst_closure C (digraph_subst u D2).

(** Heroes (Berger et al., 2013): the tournaments built from a single vertex by the operations
    H1 => H2, Δ(H,TT_k,TT_1) and Δ(TT_k,H,TT_1), where TT_k is the transitive tournament on [k]
    vertices. *)
Inductive hero : diGraph -> Prop :=
| hero_K1 : hero (transitive_tournament 1)
| hero_join (H1 H2 : diGraph) : hero H1 -> hero H2 -> hero (digraph_join H1 H2)
| hero_c3L (H : diGraph) (k : nat) :
    hero H -> hero (c3_subst H (transitive_tournament k) (transitive_tournament 1))
| hero_c3R (H : diGraph) (k : nat) :
    hero H -> hero (c3_subst (transitive_tournament k) H (transitive_tournament 1)).

(** The strong Erdős-Hajnal property of the tournament [H]: each [H]-free tournament [G] with at
    least two vertices has disjoint sets [A], [B] of linear size with all arcs from [A] to [B]. *)
Definition strong_EH_tournament (H : diGraph) : Prop :=
  exists q : nat, 1 <= q /\
    forall G : diGraph, tournament G -> ~ inhabited (H ⇀ G) -> 1 < #|G| ->
      exists A B : {set G}, [/\ [disjoint A & B], (forall a b, a \in A -> b \in B -> a -- b),
        #|G| <= q * #|A| & #|G| <= q * #|B|].

(** ** Unavoidable digraphs *)

(** Each tournament on [N] vertices contains [D]. *)
Definition tournament_unavoidable (D : diGraph) (N : nat) : Prop :=
  forall T : diGraph, tournament T -> #|T| = N -> subdigraph D T.

(** [N] is the least number such that each tournament on [N] vertices contains [D]. *)
Definition unavoidability_number (D : diGraph) (N : nat) : Prop :=
  tournament_unavoidable D N /\ (forall M : nat, M < N -> ~ tournament_unavoidable D M).

(** The unavoidability number is at most linear in the number of vertices in the class [C]
    (digraphs without unavoidability number are ignored). *)
Definition linearly_unavoidable (C : diGraph -> Prop) : Prop :=
  exists c : nat, forall (D : diGraph) (N : nat),
    C D -> unavoidability_number D N -> (N <= c * #|D|)%N.

(** The acyclic digraph [D] is a [k]-extension of [A]: the deletion of some [k] vertices gives
    [A]. *)
Definition k_extension (k : nat) (A D : diGraph) : Prop :=
  acyclic D /\ exists S : {set D}, #|S| = k /\ inhabited (induced (~: S) ≃ A).

(** * Properties *)

(** ** Acyclic digraphs *)

(** [acyclic] is the absence of directed cycles (as sequences of vertices). *)
Lemma acyclicP (D : diGraph) :
  reflect (forall c : seq D, c != [::] -> ~~ cycle (--) c) (acyclic D).
Proof.
apply: (iffP forallP) => [ac [//|u c] _|nc u].
- apply/negP; rewrite /= rcons_path => /andP[pc lu].
  have /forallP/(_ u)/implyP/(_ lu)/negP := ac (last u c).
  by apply; apply/connectP; exists c.
- apply/forallP => v; apply/implyP => uv; apply/negP => /connectP[p pp lp].
  have /negP := nc (v :: p) isT; apply.
  by rewrite /= rcons_path pp -lp.
Qed.

(** A digraph is acyclic iff it has a numbering that increases along the edges
    (a topological order). *)
Lemma acyclic_rankP (D : diGraph) :
  reflect (exists phi : D -> nat, forall u v, u -- v -> phi u < phi v) (acyclic D).
Proof.
apply: (iffP forallP) => [ac|[phi inc] u].
- exists (fun v => #|[set w | connect (--) w v]|) => u v uv.
  apply/proper_card/properP; split.
    by apply/subsetP => w; rewrite !inE => /connect_trans; apply; apply: connect1.
  exists v; rewrite !inE ?connect0 //.
  by have /forallP/(_ v)/implyP/(_ uv) := ac u.
- apply/forallP => v; apply/implyP => uv; apply/negP => /connectP[p pp lp].
  suff: phi v <= phi u by rewrite leqNgt inc.
  rewrite lp; elim: p v pp {uv lp} => //= w p IH v /andP[vw pp].
  exact: leq_trans (ltnW (inc _ _ vw)) (IH _ pp).
Qed.

(** The subdigraph induced by [A] is acyclic iff [A] has a numbering that increases along the
    edges. *)
Lemma acyclic_inducedP (D : diGraph) (A : {set D}) :
  reflect (exists phi : D -> nat, {in A &, forall u v, u -- v -> phi u < phi v})
          (acyclic (induced A)).
Proof.
apply: (iffP (acyclic_rankP _)) => -[phi inc]; last first.
  by exists (fun u => phi (val u)) => u v; apply: inc; apply: valP.
exists (fun u => if insub u is Some u' then phi u' else 0) => u v uA vA uv.
by rewrite (insubT (mem A) uA) (insubT (mem A) vA); apply: inc.
Qed.

(** ** Vertex orderings, clique number *)

(** Each injective numbering is realized, as an order, by a permutation. *)
Lemma perm_lt_ex (V : finType) (f : V -> nat) : injective f ->
  exists p : {perm V}, forall u v, perm_lt p u v = (f u < f v).
Proof.
move=> f_inj; pose below u := [set w | f w < f u].
have rk_lt u : #|below u| < #|V|.
  by rewrite -cardsT; apply/proper_card/properP; split=> //; exists u; rewrite !inE ?ltnn.
have mono u v : f u < f v -> #|below u| < #|below v|.
  move=> uv; apply/proper_card/properP; split; last by exists u; rewrite !inE ?ltnn.
  by apply/subsetP => w; rewrite !inE => wu; apply: ltn_trans uv.
pose g u : V := enum_val (Ordinal (rk_lt u)).
have g_inj : injective g.
  move=> u v /enum_val_inj/(congr1 val) /= e; apply: f_inj.
  by case: (ltngtP (f u) (f v)) => // /mono; rewrite e ltnn.
exists (perm g_inj) => u v; rewrite /perm_lt !permE !enum_valK /=.
case: (ltngtP (f u) (f v)) => [/mono //|/mono/ltnW|/f_inj->]; last by rewrite ltnn.
by rewrite leqNgt => /negbTE.
Qed.

(** A clique of a backedge graph is a set on which all arcs are backward. *)
Lemma backedge_cliqueP (D : diGraph) (p : {perm D}) (K : {set D}) :
  reflect {in K &, forall u v, perm_lt p u v -> v -- u}
          (cliqueb (K : {set backedge_graph p})).
Proof.
apply: (iffP (@cliqueP (backedge_graph p) K)) => cl u v uK vK.
- move=> uv; have uDv : u != v by apply: contraTneq uv => ->; rewrite perm_lt_irrefl.
  have /orP[/andP[]//|/andP[vu _]] := cl u v uK vK uDv.
  by have := ltn_trans uv vu; rewrite ltnn.
- move=> uDv; have : perm_lt p u v || perm_lt p v u.
    by rewrite /perm_lt -neq_ltn val_eqE (inj_eq enum_rank_inj) (inj_eq perm_inj).
  by case/orP=> h; apply/orP; [left|right]; rewrite h cl.
Qed.

(** The clique number is the minimum, over the vertex orders given by injective numberings, of
    the maximum size of a set on which all arcs are backward. *)
Lemma diclique_number_leP (D : diGraph) (k : nat) :
  diclique_number D <= k <->
  exists f : D -> nat, injective f /\
    forall K : {set D}, {in K &, forall u v, f u < f v -> v -- u} -> #|K| <= k.
Proof.
rewrite /diclique_number; case: arg_minnP => //= p _ p_min; split=> [le_k|[f [f_inj le_k]]].
- exists (fun u => val (enum_rank (p u))); split=> [u v /val_inj/enum_rank_inj/perm_inj //|K back].
  by apply: leq_trans le_k; apply: clique_bound; rewrite inE subsetT; apply/backedge_cliqueP.
- have [q qE] := perm_lt_ex f_inj; apply: leq_trans (p_min q isT) _; case: omegaP => K Kmax.
  apply: le_k => u v uK vK; rewrite -qE; apply/backedge_cliqueP: uK vK.
  by have := maxcliquesW Kmax; rewrite inE => /andP[].
Qed.

(** ** Degree sums *)

(** The sum of the outdegrees is the number of edges. *)
Lemma sum_outdeg (D : diGraph) : \sum_(v : D) outdeg v = num_edges D.
Proof.
rewrite /outdeg /num_edges -sum1_card; under eq_bigr do rewrite -sum1_card.
by rewrite pair_big_dep; apply: eq_bigl => -[u v] /=; rewrite !inE.
Qed.

(** The sum of the indegrees is the number of edges. *)
Lemma sum_indeg (D : diGraph) : \sum_(v : D) indeg v = num_edges D.
Proof.
rewrite /indeg /num_edges -sum1_card; under eq_bigr do rewrite -sum1_card.
rewrite (exchange_big_dep xpredT) // pair_big_dep.
by apply: eq_bigl => -[u v] /=; rewrite !inE.
Qed.

Lemma num_edges_digraph_of_arcs (T : finType) (A : {set T * T}) :
  num_edges (digraph_of_arcs A) = #|A|.
Proof. by apply: eq_card => -[]. Qed.
