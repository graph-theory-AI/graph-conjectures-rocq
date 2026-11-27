(** * Extremal graph theory

    Turán and Ramsey numbers, counting of copies and homomorphisms, densities, the
    Erdős-Hajnal property, Shannon capacity.  Densities and other rational numbers [a / b] are
    mostly given by two natural numbers, and the inequalities are cross-multiplied. *)

From GraphTheory Require Import preliminaries digraph sgraph dom coloring connectivity.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc homomorphism chromatic.
From GC.GraphLib Require Import digraph(oriented, automorphisms).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Turán numbers *)

(** [G] contains no graph of the family [Fam] as a subgraph. *)
Definition family_free (G : sgraph) (k : nat) (Fam : 'I_k -> sgraph) : Prop :=
  forall i : 'I_k, ~ subgraph (Fam i) G.

(** The Turán number [ex(n, Fam)] is [m]. *)
Definition turan_number (n : nat) (k : nat) (Fam : 'I_k -> sgraph) (m : nat) : Prop :=
  (exists G : sgraph, [/\ #|G| = n, #|E(G)| = m & family_free G Fam]) /\
  (forall m' : nat,
     (exists G : sgraph, [/\ #|G| = n, #|E(G)| = m' & family_free G Fam]) ->
     (m' <= m)%N).

(** [H] is a proper subgraph of [G] (up to isomorphism). *)
Definition proper_subgraph (H G : sgraph) : Prop := subgraph H G /\ ~ subgraph G H.

(** [G] is induced [H]-saturated: it has no induced subgraph isomorphic to [H], but it has one
    when any edge is added or deleted ([G] is meant to have at least two vertices). *)
Definition induced_saturated (H G : sgraph) : Prop :=
  induced_free G H /\
  (forall a b : G, a != b -> ~~ (a -- b) -> induced_free (add_edge a b) H -> False) /\
  forall e : {set G}, e \in E(G) -> induced_free (del_edges e) H -> False.

(** ** Weak saturation *)

(** The set of edges [E] contains a copy of [H] that uses the edge [e]. *)
Definition copy_through (G H : sgraph) (E : {set {set G}}) (e : {set G}) : Prop :=
  exists f : H -> G,
    [/\ injective f,
        (forall x y : H, x -- y -> [set f x; f y] \in E)
      & exists x y : H, x -- y /\ [set f x; f y] = e].

(** [F] is a weakly [H]-saturated set of edges of [G]: the other edges of [G] can be enumerated by
    a list [s] so that each of them completes a copy of [H] when it is added to [F] and to the
    edges before it. *)
Definition weakly_saturated (G H : sgraph) (F : {set {set G}}) : Prop :=
  F \subset E(G) /\
  exists s : seq {set G},
    [/\ uniq s,
        (forall e : {set G}, (e \in s) = (e \in E(G) :\: F))
      & forall i : nat, i < size s ->
          copy_through H (F :|: [set:: take i.+1 s]) (nth set0 s i)].

(** The weak saturation number wsat(G,H) (minimum size of a weakly [H]-saturated set of edges of
    [G]) is [m]. *)
Definition weak_saturation_number (G H : sgraph) (m : nat) : Prop :=
  (exists F : {set {set G}}, weakly_saturated H F /\ #|F| = m) /\
  (forall F : {set {set G}}, weakly_saturated H F -> m <= #|F|).

(** ** Graph codes *)

(** [F] is an [H]-code: a set of edge sets of graphs on [0, ..., n-1] such that the symmetric
    difference of two distinct members is never the edge set of a copy of [H]. *)
Definition graph_code (n : nat) (H : sgraph) (F : {set {set {set 'K_n}}}) : Prop :=
  (forall A, A \in F -> A \subset E('K_n)) /\
  forall A B, A \in F -> B \in F -> A != B ->
    ~ embedded_edge_copy H ((A :\: B) :|: (B :\: A)).

(** ** Ramsey numbers *)

(** [Host] arrows the family [Fam] with [k] colours: each colouring of its edges with [k]
    colours has a monochromatic copy of a graph of [Fam]. *)
Definition ramsey_arrows (Host : sgraph) (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall col : {set Host} -> 'I_k,
    exists (i : 'I_r) (c : 'I_k), subgraph (Fam i) (edge_color_class col (pred1 c)).

(** The Ramsey number of the family [Fam] with [k] colours is [n]. *)
Definition ramsey_number (k r : nat) (Fam : 'I_r -> sgraph) (n : nat) : Prop :=
  ramsey_arrows 'K_n k Fam /\ forall m : nat, m < n -> ~ ramsey_arrows 'K_m k Fam.

(** The family [Fam] is [k]-nice: the graphs whose chromatic number is the Ramsey number of [Fam]
    with [k] colours arrow [Fam] with [k] colours. *)
Definition ramsey_nice (k r : nat) (Fam : 'I_r -> sgraph) : Prop :=
  forall n : nat, ramsey_number k Fam n ->
    forall G : sgraph, χ([set: G]) = n -> ramsey_arrows G k Fam.

(** For some lists of [k] colours on the edges of [Host], each colouring of the edges from these
    lists has a monochromatic copy of [H]. *)
Definition list_ramsey_arrows (Host : sgraph) (k : nat) (H : sgraph) : Prop :=
  exists (C : finType) (L : {set Host} -> {set C}),
    (forall e : {set Host}, #|L e| = k) /\
    forall col : {set Host} -> C,
      (forall e : {set Host}, col e \in L e) ->
      exists c : C, subgraph H (edge_color_class col (pred1 c)).

(** The list Ramsey number of [H] with [k] colours is [n] ([0 < k] is meant). *)
Definition list_ramsey_number (k : nat) (H : sgraph) (n : nat) : Prop :=
  list_ramsey_arrows 'K_n k H /\ forall m : nat, m < n -> ~ list_ramsey_arrows 'K_m k H.

(** The injective homomorphisms from [H] to [G]. *)
Definition injective_homs (H G : sgraph) : {set {ffun H -> G}} :=
  [set f : {ffun H -> G} |
    injectiveb f & [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]].

(** The number of copies of [H] in [G], as subgraphs. *)
Definition copy_count (H G : sgraph) : nat :=
  #|injective_homs H G| %/ #|automorphisms H|.

(** The number of copies of [H] in [G] and in its complement. *)
Definition mono_copy_count (H G : sgraph) : nat := copy_count H G + copy_count H (compl G).

(** The threshold Ramsey multiplicity of [H] is [m]: the minimum number of monochromatic copies
    of [H] in a 2-colouring of the edges of a complete graph whose number of vertices is the
    Ramsey number of [H] with 2 colours. *)
Definition threshold_multiplicity (H : sgraph) (m : nat) : Prop :=
  exists R : nat, [/\ ramsey_number 2 (fun _ : 'I_1 => H) R,
    forall G : sgraph, #|G| = R -> m <= mono_copy_count H G
  & exists2 G : sgraph, #|G| = R & mono_copy_count H G = m].

(** ** Counting *)

(** [B] is Sidorenko among oriented graphs: the density of homomorphisms from
    [B] to any oriented graph is at least the power [num_edges B] of its density. *)
Definition directed_sidorenko (B : diGraph) : Prop :=
  forall D : diGraph,
    oriented D ->
    num_edges D ^ num_edges B * #|D| ^ #|B|
      <= hom_count B D * #|D| ^ (2 * num_edges B).

(** [H] is common: the density of homomorphisms from [H] to a large graph plus the density to its
    complement is at least [2^(1 - m)] (up to [o(1)]), where [m] is the number of edges of [H]. *)
Definition common_graph (H : sgraph) : Prop :=
  forall m : nat, 0 < m -> eventually (fun n =>
    forall G : sgraph, #|G| = n ->
      2 * m * n ^ #|H| <= m * 2 ^ #|E(H)| * (hom_count H G + hom_count H (compl G)) + n ^ #|H|).

(** The number of spanning trees of [G]. *)
Definition spanning_tree_count (G : sgraph) : nat := #|[set T : {set {set G}} | spanning_tree T]|.

(** The number of cycles of length [L] of [G] ([3 <= L] is meant). *)
Definition cycle_count_length (G : sgraph) (L : nat) : nat :=
  #|[set t : L.-tuple G | ucycleb (--) (val t)]| %/ (2 * L).

(** The number of cycles of [G]. *)
Definition cycle_count (G : sgraph) : nat := \sum_(3 <= L < #|G|.+1) cycle_count_length G L.

(** [c] is a peripheral cycle: an induced cycle whose deletion leaves a connected graph. *)
Definition peripheral_cycle (G : sgraph) (c : seq G) : Prop :=
  chordless_cycle c /\ connected (~: [set x in c]).

(** ** Densities, homogeneous sets *)

(** The maximum density [m(H)] of [H] is at most [a / b]: so is the ratio of the number of
    edges to the number of vertices for all its induced subgraphs. *)
Definition max_density_le (H : sgraph) (a b : nat) : Prop :=
  forall S : {set H}, b * #|E(induced S)| <= a * #|S|.

(** The largest [s] such that [G] has a subgraph [K_s,s], not necessarily induced. *)
Definition biclique_number (G : sgraph) : nat :=
  \max_(s < #|G|.+1 | [exists A : {set G}, exists B : {set G},
                         [&& #|A| == s, #|B| == s & complete_between A B]]) s.

(** The largest [t] such that [G] has a subgraph isomorphic to the complete [d]-partite graph with
    parts of size [t] is [t]. *)
Definition multipartite_number (G : sgraph) (d t : nat) : Prop :=
  subgraph (complete_multipartite d t) G /\
  forall s : nat, subgraph (complete_multipartite d s) G -> s <= t.

(** The class [F] is degree-bounded: on its graphs, the average degree is bounded by a function
    of the biclique number. *)
Definition degree_bounded (F : sgraph -> Prop) : Prop :=
  exists g : nat -> nat, forall G : sgraph, F G -> 2 * #|E(G)| <= #|G| * g (biclique_number G).

(** [G] has a nonempty bipartite induced subgraph of minimum degree at least [d]. *)
Definition dense_bipartite_induced (G : sgraph) (d : nat) : Prop :=
  exists S : {set G}, [/\ S != set0, bipartite (induced S) & min_degree_ge (induced S) d].

(** [G] is [p/d]-bounded: the closed neighbourhoods have less than [(p / d) |G|] vertices. *)
Definition eps_bounded (G : sgraph) (p d : nat) : Prop :=
  forall v : G, d * #|N[v]| < p * #|G|.

(** [S] is homogeneous: a clique or a stable set. *)
Definition homogeneous_set (G : sgraph) (S : {set G}) : Prop :=
  clique S \/ stable S.

(** [X] is [a/b]-restricted: in [G] or in its complement, the maximum degree of the subgraph
    induced by [X] is at most [(a / b) |X|]. *)
Definition restricted_set (G : sgraph) (a b : nat) (X : {set G}) : Prop :=
  b * Delta (induced X) <= a * #|X| \/ b * Delta (@induced (compl G) X) <= a * #|X|.

(** The disjoint sets [A] and [B] have density at most [a / b]. *)
Definition sparse_pair (G : sgraph) (A B : {set G}) (a b : nat) : Prop :=
  [disjoint A & B] /\
  b * edge_count_between A B <= a * (#|A| * #|B|).

(** [H] has the sparse strong Erdős-Hajnal property: for some [eps > 0], each graph with at
    least two vertices and no induced [H] has a vertex of degree at least [eps |G|], or two
    anticomplete sets of size at least [eps |G|]. *)
Definition sparse_strong_EH (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

(** The set [S] is shattered by the neighbourhoods of the vertices. *)
Definition shattered (G : sgraph) (S : {set G}) : Prop :=
  forall T : {set G}, T \subset S -> exists v : G, N(v) :&: S = T.

(** The VC-dimension of [G] is at most [d]. *)
Definition vc_dim_le (G : sgraph) (d : nat) : Prop :=
  forall S : {set G}, shattered S -> #|S| <= d.

(** ** Shannon capacity *)

(** The [n]-th strong power of [G]: distinct tuples whose components are equal or adjacent are
    adjacent. *)
Definition strong_power (G : sgraph) (n : nat) : sgraph :=
  @sgraph_of_rel {ffun 'I_n -> G} (fun x y => [forall i, (x i == y i) || (x i -- y i)]).

(** The Shannon capacity of [G] is [c], the least upper bound of [alpha(G^n)^(1/n)]. *)
Definition shannon_capacity (R : realFieldType) (G : sgraph) (c : R) : Prop :=
  (forall n, (0 < n)%N -> (α([set: strong_power G n])%:R <= c ^+ n)%R) /\
  (forall b : R, (forall n, (0 < n)%N -> (α([set: strong_power G n])%:R <= b ^+ n)%R) ->
     (c <= b)%R).

(** ** Good edge labellings *)

(** [p] is a nonempty path from [u] to [v] whose labels are increasing. *)
Definition increasing_path (G : sgraph) (l : G -> G -> nat) (u v : G) (p : seq G) : bool :=
  [&& uniq (u :: p), path (--) u p, last u p == v,
      sorted ltn (pairmap l u p) & p != [::] ].

(** [G] has a good edge labelling: the labels are distinct and, for all vertices [u] and [v],
    there is at most one increasing path from [u] to [v]. *)
Definition good_edge_labeling (G : sgraph) : Prop :=
  exists l : G -> G -> nat,
    [/\ (forall x y : G, l x y = l y x),
        (forall x y x' y' : G,
            x -- y -> x' -- y' -> x != y -> x' != y' ->
            l x y = l x' y' -> [set x; y] == [set x'; y']) &
        (forall (u v : G) (p q : seq G),
            increasing_path l u v p -> increasing_path l u v q -> p = q) ].

(** ** Dimension of incidence posets *)

(** The incidence order of the hypergraph [E]: a vertex is below the edges that contain it (the
    sets that are not in [E] are isolated elements). *)
Definition incidence_order (T : finType) (E : {set {set T}}) : rel (T + {set T}) :=
  fun x y =>
    match x, y with
    | inl v, inl w => v == w
    | inl v, inr e => (e \in E) && (v \in e)
    | inr e, inr f => e == f
    | inr _, inl _ => false
    end.

(** ** VC-dimension of induced subgraphs *)

(** An induced embedding maps shattered sets to shattered sets. *)
Lemma shattered_isubgraph (F G : sgraph) (i : F ⇀ G) (S : {set F}) :
  shattered S -> shattered (i @: S).
Proof.
move=> shS T /subsetP TS; have [v vS] : exists v, N(v) :&: S = [set x in S | i x \in T].
  by apply: shS; rewrite setIdE subsetIl.
exists (i v); apply/setP => y; rewrite !inE; apply/idP/idP => [/andP[vy /imsetP[u uS yu]]|yT].
  have : u \in N(v) :&: S by rewrite !inE -(isubgraph_mono i) -yu vy uS.
  by rewrite vS inE -yu => /andP[].
have [u uS yu] := imsetP (TS y yT); rewrite yu imset_f // andbT isubgraph_mono.
have : u \in [set x in S | i x \in T] by rewrite inE uS -yu.
by rewrite -vS !inE => /andP[].
Qed.

(** The VC-dimension of an induced subgraph is at most that of the graph. *)
Lemma vc_dim_le_isubgraph (F G : sgraph) (i : F ⇀ G) (d : nat) :
  vc_dim_le G d -> vc_dim_le F d.
Proof.
by move=> vcG S /(shattered_isubgraph (i := i))/vcG; rewrite card_imset //; apply: isubgraph_inj.
Qed.

(** ** Edge counts *)

Section TreeEdges.
Variable T : sgraph.
Hypothesis treeT : is_tree [set: T].

(** A tree with [n] vertices has [n - 1] edges: rooting it at [r], each vertex [z] other than [r]
    is joined by an edge to a unique parent, the vertex before [z] on the path from [r] to [z]. *)
Lemma tree_card_edges (r : T) : #|E(T)|.+1 = #|T|.
Proof.
have pathT x : exists p : Path r x, irred p.
  by apply/connect_irredP; exact: connectedTE treeT.2 r x.
pose R := [set p : T * T | p.1 -- p.2 && connect (restrict (predC1 p.2) (--)) r p.1].
have pathR u z : (u, z) \in R -> exists2 q : Path r u, irred q & z \notin q.
  rewrite inE /= => /andP[uz]; case: (eqVneq r u) uz => [<- rz _|ru uz].
    by exists (idp r); rewrite ?irred_idp // mem_idp eq_sym sg_edgeNeq.
  case/connect_irredRP => // q Iq /subsetP qz; exists q => //.
  by apply/negP => /qz; rewrite inE eqxx.
have pathRz u z (uz : u -- z) : (u, z) \in R ->
    exists q : Path r u, [/\ irred (pcat q (edgep uz)), z \notin q & u \in q].
  by case/pathR => q Iq zq; exists q; rewrite irred_edgeR zq Iq path_end.
have uniqR u u' z : (u, z) \in R -> (u', z) \in R -> u = u'.
  move=> uzR u'zR; move: (uzR) (u'zR); rewrite !inE /= => /andP[uz _] /andP[u'z _].
  case/(pathRz _ _ uz): uzR => q [Iq _ _]; case/(pathRz _ _ u'z): u'zR => q' [Iq' _ _].
  have /(congr1 val) /= := forestT_unique treeT.1 Iq Iq'; rewrite !cats1 => /rcons_inj[].
  by move=> /(congr1 (last r)); rewrite !path_last.
have ER : E(T) = [set [set p.1; p.2] | p in R].
  apply/setP => e; apply/edgesP/imsetP => [[x [y [-> xy]]]|[[u z] + ->]]; last first.
    by rewrite inE /= => /andP[uz _]; exists u, z.
  have [p Ip] := pathT x; have [yp|yp] := boolP (y \in p); last first.
    exists (x, y) => //; rewrite inE /= xy; apply: (connectRI p) => v vp; rewrite inE.
    by apply: contraNneq yp => <-.
  case/(isplitP Ip): yp => p1 p2 _ _ p12; exists (y, x); last by rewrite /= setUC.
  rewrite inE /= sg_sym xy; apply: (connectRI p1) => v vp; rewrite inE.
  apply: contraTneq vp => ->; apply/negP => /p12 /(_ (path_end p2)) xy'.
  by rewrite xy' sg_irrefl in xy.
rewrite -cardsT (cardsD1 r) inE add1n ER card_in_imset; last first.
  rewrite -(card_in_imset (f := snd)) => [[u z] [u' z'] uzR u'z'R /= zz'|].
    by move: uzR; rewrite zz' => /uniqR /(_ u'z'R) ->.
  congr _.+1; apply/eq_card => z; rewrite !inE andbT eq_sym.
  apply/imsetP/idP => [[[u z'] + ->]|zr].
    rewrite inE /= => /andP[uz /connect_restrict_case[ru|[_ + _ _]]].
      by rewrite ru sg_edgeNeq.
    by rewrite inE.
  have [p Ip] := pathT z; have [u [p' [uz Ep]]] := splitR p (zr : r != z); exists (u, z) => //.
  rewrite inE /= uz; apply: (connectRI p') => v vp; rewrite inE.
  by move: Ip; rewrite Ep irred_edgeR => /andP[+ _]; apply: contraNneq => <-.
move=> [u z] [z' u'] uzR zuR /= /doubleton_eq_iff[[-> ->] //|[eu ez]].
rewrite -{}eu -{}ez in zuR *.
have uz : u -- z by move: uzR; rewrite inE => /andP[].
have [q [Iq _ uq]] := pathRz _ _ uz uzR; have [q' Iq' uq'] := pathR _ _ zuR.
by move: uq'; rewrite -(forestT_unique treeT.1 Iq Iq') mem_pcat uq.
Qed.

End TreeEdges.

(** The edges of a colour class are the edges whose colour satisfies [p]. *)
Lemma edge_color_class_edges (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) :
  E(edge_color_class col p) = [set e in E(G) | p (col e)].
Proof.
apply/setP => e; rewrite inE; apply/edgesP/andP => [[x [y [-> xy]]]|[/edgesP[x [y [-> xy]]] pe]].
  by move: xy; rewrite edge_color_classE => /andP[xy ->]; rewrite (@in_edges G).
by exists x, y; rewrite edge_color_classE xy.
Qed.
