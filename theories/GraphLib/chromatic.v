(** * Colourings

    Colourings of the vertices or of the edges of simple graphs ([sgraph]) and of multigraphs
    ([mgraph]), list colourings and their variants, chi-boundedness, fractional and circular
    colourings.  The chromatic number [χ(A)], the clique number [ω(A)] and the independence
    number [α(A)] of a set [A] of vertices are those of GraphTheory ([coloring]); [A] is
    [[set: G]] for the whole graph.

    A colouring of the edges of a simple graph is a map [col] on the sets of vertices:
    [col [set x; y]] is the colour of the edge [xy], and the other values are irrelevant. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring connectivity.
From GraphTheory Require skeleton.
From mathcomp Require Import boot order algebra.
From GC.GraphLib Require Import misc hypergraph.
From GC.GraphLib Require Import digraph(outdeg, balanced_digraph, digraph_of_arcs).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Colourings of the vertices *)

(** [col] is a proper colouring of [G]. *)
Definition proper_coloring (G : sgraph) (C : finType) (col : G -> C) : bool :=
  coloring (preim_partition col [set: G]) [set: G].

(** The number of proper colourings of [G] with [k] colours. *)
Definition num_colorings (G : sgraph) (k : nat) : nat :=
  #|[set c : {ffun G -> 'I_k} | proper_coloring c]|.

(** All elements of [S] have the same colour. *)
Definition monochromatic_on (T : finType) (C : eqType)
    (col : T -> C) (S : {set T}) : bool :=
  constant [seq col x | x <- enum S].

(** The colours of the neighbours of [v]. *)
Definition neighbor_colors (G : sgraph) (C : finType) (col : G -> C) (v : G) : {set C} :=
  [set c : C | [exists u : G, (u -- v) && (col u == c)]].

(** [col] is a [k]-homogeneous colouring: it is proper, and the neighbours of each vertex have
    [k] colours. *)
Definition homogeneous_coloring (G : sgraph) (C : finType) (col : G -> C) (k : nat) : Prop :=
  proper_coloring col /\ forall v : G, #|neighbor_colors col v| = k.

(** [G] has a [k]-homogeneous colouring. *)
Definition homogeneous_colorable (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (col : G -> C), homogeneous_coloring col k.

(** [G] is vertex-critical: deleting any vertex decreases the chromatic number. *)
Definition vertex_critical (G : sgraph) : Prop := forall v : G, χ([set: G] :\ v) < χ([set: G]).

(** [G] is double-critical: deleting both ends of any edge decreases the chromatic number
    by 2. *)
Definition double_critical (G : sgraph) : Prop :=
  forall x y : G, x -- y -> χ([set: G] :\: [set x; y]) + 2 = χ([set: G]).

(** [G] is strongly [r]-colourable: for each partition of its vertices in parts of size at most
    [r], it has a proper [r]-colouring that is injective on the parts. *)
Definition strongly_colorable (G : sgraph) (r : nat) : Prop :=
  forall P : {set {set G}},
    partition P [set: G] -> (forall B : {set G}, B \in P -> #|B| <= r) ->
    exists f : G -> 'I_r,
      (forall x y : G, x -- y -> f x != f y) /\
      (forall B : {set G}, B \in P -> {in B &, injective f}).

(** [G] has a colouring with [k] colours whose classes are cliques or stable sets. *)
Definition cocolorable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k,
    forall i : 'I_k,
      let S := [set v : G | col v == i] in
      clique S \/ stable S.

(** The cochromatic number of [G] is [k]. *)
Definition cochromatic_number (G : sgraph) (k : nat) : Prop :=
  cocolorable G k /\
  forall j : nat, cocolorable G j -> k <= j.

(** [G] has a colouring with [k] colours whose monochromatic components have at most [c]
    vertices. *)
Definition clustered_colorable (G : sgraph) (k c : nat) : Prop :=
  exists col : G -> 'I_k,
    forall S : {set G},
      connected S -> monochromatic_on col S -> #|S| <= c.

(** The clustered chromatic number of the class [F] is at most [k]: its graphs have colourings
    with [k] colours whose monochromatic components are bounded. *)
Definition clustered_chromatic_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists c : nat, forall G : sgraph, F G -> clustered_colorable G k c.

(** The defective chromatic number of the class [F] is at most [k]: its graphs have colourings
    with [k] colours whose monochromatic subgraphs have bounded maximum degree. *)
Definition defective_chromatic_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists m : nat,
    forall G : sgraph, F G ->
      exists col : G -> 'I_k,
        forall v : G, #|N(v) :&: [set u : G | col u == col v]| <= m.

(** The coefficient of [x_0^(a 0) x_1^(a 1) ...] in the chromatic symmetric function of [G]
    with [k] variables: the number of proper colourings with [a i] vertices of colour [i]. *)
Definition chromatic_symmetric_coeff (G : sgraph) (k : nat) (a : 'I_k -> nat) : nat :=
  #|[set c : {ffun G -> 'I_k} |
       proper_coloring c && [forall b : 'I_k, #|[set x | c x == b]| == a b]]|.

(** [G] and [H] have the same chromatic symmetric function. *)
Definition same_chromatic_symmetric (G H : sgraph) : Prop :=
  forall (k : nat) (a : 'I_k -> nat), chromatic_symmetric_coeff G a = chromatic_symmetric_coeff H a.

(** [S] is a Kempe chain of [col] for the colours [a] and [b]: a component of the subgraph
    induced by these colours. *)
Definition kempe_chain (G : sgraph) (k : nat) (col : G -> 'I_k) (a b : 'I_k)
    (S : {set G}) : Prop :=
  S \in components [set v | (col v == a) || (col v == b)].

(** [col'] is obtained from [col] by exchanging the two colours of a Kempe chain. *)
Definition kempe_change (G : sgraph) (k : nat) (col col' : G -> 'I_k) : Prop :=
  exists (a b : 'I_k) (S : {set G}),
    [/\ a != b, kempe_chain col a b S &
        forall v : G, col' v = if v \in S then (if col v == a then b else a) else col v].

(** [col'] is obtained from [col] by at most [n] Kempe changes. *)
Fixpoint kempe_reach_le (G : sgraph) (k n : nat) (col col' : G -> 'I_k) {struct n} : Prop :=
  match n with
  | 0 => col =1 col'
  | n'.+1 =>
      col =1 col' \/ exists c : G -> 'I_k, kempe_change col c /\ kempe_reach_le n' c col'
  end.

(** ** Weighted colourings *)

(** The maximum weight of a clique, for the weights [p], is [w]. *)
Definition weighted_clique_number (G : sgraph) (p : G -> nat) (w : nat) : Prop :=
  (exists Q : {set G}, clique Q /\ \sum_(v in Q) p v = w) /\
  (forall Q : {set G}, clique Q -> \sum_(v in Q) p v <= w).

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** The weighted chromatic number is [k]. *)
Definition weighted_chromatic_number (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  weighted_colorable p k /\ (forall m : nat, weighted_colorable p m -> k <= m).

(** ** List colourings

    A list assignment is a map [L : G -> {set C}] for some finite set [C] of colours. *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** The choice number of [G] is its chromatic number. *)
Definition chromatic_choosable (G : sgraph) : Prop := choice_number G (χ([set: G])).

(** [f] is an acyclic colouring from the lists [L]. *)
Definition acyclic_list_coloring (G : sgraph) (C : finType) (L : G -> {set C})
    (f : G -> C) : Prop :=
  proper_list_coloring L f /\
  forall c : seq G, seq_cycle (--) c -> 2 < size (undup [seq f x | x <- c]).

(** [G] is acyclically [k]-choosable. *)
Definition acyclically_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) ->
    exists f : G -> C, acyclic_list_coloring L f.

(** The lists have size [k], and those of adjacent vertices have at most one common colour. *)
Definition separated_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (k : nat) : Prop :=
  (forall v : G, #|L v| = k) /\
  forall u v : G, u -- v -> #|L u :&: L v| <= 1.

(** [G] can be coloured from all separated lists of size [k]. *)
Definition separation_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    separated_lists L k -> list_colorable L.

(** The set [A] of vertices can be coloured on line, [f v] being the number of times that [v]
    may be presented: at each turn, the opponent presents a nonempty set [M] of uncoloured
    vertices, and a stable subset [I] of [M] is coloured.  The number of turns is at most
    [n]. *)
Fixpoint paintable_within (G : sgraph) (n : nat) (A : {set G}) (f : G -> nat)
    {struct n} : bool :=
  match n with
  | 0 => A == set0
  | n'.+1 =>
      (A == set0) ||
      ([forall v, (v \in A) ==> (0 < f v)] &&
       [forall M : {set G},
          (M \subset A) ==> (M != set0) ==>
          [exists I : {set G},
             [&& I \subset M, stable I &
                 @paintable_within G n' (A :\: I)
                   (fun v => if v \in M then (f v).-1 else f v)]]])
  end.

(** [G] is [f]-paintable (the number of turns is large enough not to matter). *)
Definition paintable (G : sgraph) (f : G -> nat) : Prop :=
  @paintable_within G (\sum_(v in [set: G]) (f v).+1) [set: G] f.

(** [G] is [k]-paintable (on-line [k]-choosable). *)
Definition k_paintable (G : sgraph) (k : nat) : Prop :=
  @paintable G (fun _ : G => k).

(** The on-line choice number (paint number) of [G] is [m]. *)
Definition online_choice_number (G : sgraph) (m : nat) : Prop :=
  k_paintable G m /\ (forall k, k_paintable G k -> m <= k).

(** The total weight of the requests [w] (the vertex [v] requests the colour [c] with weight
    [w v c]), for the colours in the lists [L]. *)
Definition total_request_weight
    (G : sgraph) (C : finType) (L : G -> {set C}) (w : G -> C -> nat) : nat :=
  \sum_(v : G) \sum_(c in L v) w v c.

(** The weight of the requests satisfied by the colouring [f]. *)
Definition satisfied_request_weight
    (G : sgraph) (C : finType) (w : G -> C -> nat) (f : G -> C) : nat :=
  \sum_(v : G) w v (f v).

(** [G] is weighted [p/q]-flexible for lists of size [k]: for all requests, some proper list
    colouring satisfies a proportion at least [p/q] of their weight. *)
Definition weighted_flexible (G : sgraph) (k p q : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}) (w : G -> C -> nat),
    (forall v : G, #|L v| = k) ->
    exists f : G -> C,
      proper_list_coloring L f /\
      p * total_request_weight L w <= q * satisfied_request_weight w f.

(** ** Correspondence colourings (DP-colourings)

    [C u v a b] means that the colours [a] of [u] and [b] of [v] are in conflict, for
    adjacent vertices [u] and [v]. *)

(** [G] has a colouring with [k] colours that avoids the conflicts [C]. *)
Definition conflict_colorable
    (G : sgraph) (k : nat) (C : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  exists col : G -> 'I_k,
    forall u v : G, u -- v -> ~~ C u v (col u) (col v).

(** [C] is a correspondence assignment: for each edge, the conflicts are symmetric and form a
    matching. *)
Definition correspondence_assignment
    (G : sgraph) (k : nat) (C : G -> G -> 'I_k -> 'I_k -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_k, C u v a b = C v u b a) /\
  (forall (u v : G) (a b1 b2 : 'I_k),
    u -- v -> C u v a b1 -> C u v a b2 -> b1 = b2) /\
  (forall (u v : G) (a1 a2 b : 'I_k),
    u -- v -> C u v a1 b -> C u v a2 b -> a1 = a2).

(** [G] is correspondence [k]-colourable (DP-[k]-colourable). *)
Definition correspondence_colorable (G : sgraph) (k : nat) : Prop :=
  forall C : G -> G -> 'I_k -> 'I_k -> bool,
    correspondence_assignment C -> conflict_colorable C.

(** ** The Alon-Tarsi number *)

(** The Eulerian subsets of the arc set [A]: indegrees and outdegrees are equal. *)
Definition eulerian_subsets (V : finType) (A : {set V * V}) : {set {set V * V}} :=
  [set B : {set V * V} | (B \subset A) && balanced_digraph (digraph_of_arcs B)].

(** [A] is an Alon-Tarsi orientation: it has not the same numbers of Eulerian subsets with an
    even number of arcs and with an odd number of arcs. *)
Definition alon_tarsi (V : finType) (A : {set V * V}) : bool :=
  #|[set B in eulerian_subsets A | ~~ odd #|B|]| != #|[set B in eulerian_subsets A | odd #|B|]|.

(** The Alon-Tarsi number of [G] is at most [k]: [G] has an Alon-Tarsi orientation with
    outdegrees less than [k]. *)
Definition alon_tarsi_number_le (G : sgraph) (k : nat) : Prop :=
  exists A : {set G * G},
    [/\ forall x y : G, (x, y) \in A -> x -- y,
        forall x y : G, x -- y -> ((x, y) \in A) (+) ((y, x) \in A),
        alon_tarsi A &
        forall v : G, (outdeg (D := digraph_of_arcs A) v).+1 <= k].

(** ** Chi-boundedness *)

(** The class [F] is chi-bounded: on its graphs, the chromatic number is bounded by a function
    of the clique number. *)
Definition chi_bounded (F : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, F G -> χ([set: G]) <= f (ω([set: G])).

(** The class [F] is polynomially chi-bounded. *)
Definition poly_chi_bounded (F : sgraph -> Prop) : Prop :=
  exists c d : nat,
    forall G : sgraph, F G -> χ([set: G]) <= c * ω([set: G]) ^ d.

(** The set [F] of integers is [k]-constricting: the graphs of large chromatic number and of
    clique number less than [k] have a hole whose length is in [F]. *)
Definition k_constricting (F : nat -> Prop) (k : nat) : Prop :=
  exists n : nat, forall G : sgraph,
    n <= χ([set: G]) ->
    k <= ω([set: G]) \/ exists L : nat, F L /\ has_hole_of_length G L.

(** [F] is constricting. *)
Definition constricting (F : nat -> Prop) : Prop := forall k : nat, k_constricting F k.

(** ** Fractional colourings *)

(** The fractional chromatic number of [G] is at most [p / q] ([0 < q] is meant): [G] has a
    [b]-fold colouring with [a] colours (each vertex receives [b] colours, and adjacent vertices
    receive disjoint sets) such that [a / b <= p / q]. *)
Definition fractional_chromatic_le (G : sgraph) (p q : nat) : Prop :=
  exists a b : nat, [/\ 0 < b, weighted_colorable (fun _ : G => b) a & a * q <= p * b].

(** The fractional chromatic number of [G] is at least the integer [k]. *)
Definition fractional_chromatic_ge (G : sgraph) (k : nat) : Prop :=
  forall a b : nat, 0 < b -> weighted_colorable (fun _ : G => b) a -> k * b <= a.

(** The fractional chromatic number of [G] is [r]. *)
Definition fractional_chromatic_number (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\
     weighted_colorable (fun _ : G => b) a /\ r = (a%:Q / b%:Q)%R) /\
  (forall a b : nat, (0 < b)%N ->
     weighted_colorable (fun _ : G => b) a -> (r <= a%:Q / b%:Q)%R).

(** The Hall ratio of [G] is at most [p / q]: so is the ratio of the number of vertices to the
    independence number for all its subgraphs. *)
Definition hall_ratio_le (G : sgraph) (p q : nat) : Prop :=
  forall H : sgraph, subgraph H G -> q * #|H| <= p * α([set: H]).

(** ** Circular colourings

    They are defined for a relation [adj] on a type [V], possibly infinite. *)

(** [c] is a circular [(p,q)]-colouring: its values are less than [p] and, for adjacent
    vertices, they differ by at least [q] and at most [p - q]. *)
Definition circular_coloring (V : Type) (adj : V -> V -> bool) (p q : nat) (c : V -> nat) : Prop :=
  (forall v, (c v < p)%N) /\
  (forall u v, adj u v ->
     (q <= absz (Posz (c u) - Posz (c v))%R)%N /\
     (absz (Posz (c u) - Posz (c v))%R <= p - q)%N).

(** The circular chromatic number is [r]: the least [p / q] such that there is a circular
    [(p,q)]-colouring (there is none if no two vertices are adjacent). *)
Definition circular_chromatic_number (V : Type) (adj : V -> V -> bool) (r : rat) : Prop :=
  (exists p q : nat, (0 < q)%N /\ (exists c, circular_coloring adj p q c) /\ r = (p%:Q / q%:Q)%R) /\
  (forall p q : nat, (0 < q)%N -> (exists c, circular_coloring adj p q c) -> (r <= p%:Q / q%:Q)%R).

(** [G] is circularly [t]-choosable: for all [p] and [q], it has a circular [(p,q)]-colouring
    from all lists of size at least [t * q]. *)
Definition circularly_choosable (G : sgraph) (t : rat) : Prop :=
  forall p q : nat, (0 < q)%N ->
    forall L : G -> {set 'I_p},
      (forall v, (t * q%:Q <= (#|L v|)%:Q)%R) ->
      exists c : G -> 'I_p,
        circular_coloring (fun x y : G => x -- y) p q (fun v => (c v : nat)) /\
        (forall v, c v \in L v).

(** The circular choosability of [G] is [b]: the greatest lower bound of the [t >= 1] such that
    [G] is circularly [t]-choosable. *)
Definition circular_choosability (G : sgraph) (b : rat) : Prop :=
  [/\ (1 <= b)%R,
      (forall t : rat, (b < t)%R -> circularly_choosable G t)
    & (forall t : rat, (1 <= t)%R -> circularly_choosable G t -> (b <= t)%R)].

(** ** Colourings of the edges of simple graphs *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** The spanning subgraph formed by the edges with colour in [p]. *)
Definition edge_color_class (G : sgraph) (C : eqType) (col : {set G} -> C) (p : pred C) : sgraph :=
  del_edge_set [set e : {set G} | ~~ p (col e)].

(** [G] is [Δ]-edge-critical (or edge-chromatic critical), for its maximum degree [Δ]: it is not
    [Δ]-edge-colourable, but it is after the deletion of any edge ([G] may be disconnected). *)
Definition Delta_edge_critical (G : sgraph) : Prop :=
  Delta G < χ([set: simple_line_graph G]) /\
  forall e : simple_line_graph G, χ([set: simple_line_graph G] :\ e) <= Delta G.

(** The strong chromatic index of [G]: the chromatic number of the square of its line graph. *)
Definition strong_chromatic_index (G : sgraph) : nat :=
  χ([set: graph_power (simple_line_graph G) 2]).

(** [col] is an acyclic edge colouring: it is proper, and each cycle has at least three
    colours. *)
Definition acyclic_edge_coloring (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  proper_edge_coloring col /\
  forall s : seq G, seq_cycle (--) s -> 2 < size (undup (map col (seq_cycle_edge_list s))).

(** [col] is a star edge colouring: it is proper, and no path or cycle with four edges has only
    two colours. *)
Definition star_edge_coloring (G : sgraph) (C : finType) (col : {set G} -> C) : Prop :=
  [/\ proper_edge_coloring col,
      (forall a b c d e : G,
         uniq [:: a; b; c; d; e] -> a -- b -> b -- c -> c -- d -> d -- e ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; e]]|)
    & (forall a b c d : G,
         uniq [:: a; b; c; d] -> a -- b -> b -- c -> c -- d -> d -- a ->
         2 < #|[set col [set a; b]; col [set b; c]; col [set c; d]; col [set d; a]]|)].

(** [G] is star [k]-edge-colourable ([0 < k] is meant). *)
Definition star_edge_colorable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k, star_edge_coloring col.

(** The star chromatic index of [G] is [k]. *)
Definition star_chromatic_index (G : sgraph) (k : nat) : Prop :=
  star_edge_colorable G k /\
  (forall k', star_edge_colorable G k' -> (k <= k')%N).

(** The sum of the colours of the edges incident to [v], the colours being numbered from 1. *)
Definition incident_sum
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) : nat :=
  \sum_(e in [set e in E(G) | v \in e]) (val (col e)).+1.

(** [col] is neighbour sum distinguishing: adjacent vertices have different sums. *)
Definition neighbor_sum_distinct
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall x y : G, x -- y -> incident_sum col x != incident_sum col y.

(** The path [p] is rainbow: its edges have distinct colours. *)
Definition rainbow_path
    (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) : Prop :=
  seq_simple_path p /\ uniq (map col (seq_edge_list p)).

Section TotalGraph.
Variable G : sgraph.

(** Adjacent vertices, distinct edges with a common end, or an edge and one of its ends. *)
Definition total_graph_rel : rel (G + simple_line_graph G)%type :=
  fun a b =>
    match a, b with
    | inl x, inl y => x -- y
    | inr e, inr f => e -- f
    | inl x, inr e => x \in val e
    | inr e, inl x => x \in val e
    end.

Lemma total_graph_sym : symmetric total_graph_rel.
Proof. by move=> [x|e] [y|f] //=; rewrite sg_sym. Qed.

Lemma total_graph_irrefl : irreflexive total_graph_rel.
Proof. by move=> [x|e] //=; rewrite sg_irrefl. Qed.

(** The total graph of [G], whose proper colourings are the total colourings of [G]. *)
Definition total_graph : sgraph := SGraph total_graph_sym total_graph_irrefl.

End TotalGraph.

(** ** Colourings of the edges of multigraphs *)

(** The chromatic index of [G] ([0] for [G] without edges; loops are allowed). *)
Definition mchromatic_index (G : mgraph) : nat := χ([set: mline_graph G]).

(** The edges of the total graph of a multigraph ([sk_rel]: distinct and adjacent vertices). *)
Definition mtotal_rel (G : mgraph) : rel (G + edge G)%type :=
  fun a b =>
    match a, b with
    | inl x, inl y => skeleton.sk_rel x y
    | inr e, inr f => @mline_rel G e f
    | inl x, inr e => incident x e
    | inr e, inl x => incident x e
    end.

Lemma mtotal_rel_sym (G : mgraph) : symmetric (@mtotal_rel G).
Proof.
move=> [x|e] [y|f] //=.
- by rewrite skeleton.sk_rel_sym.
- by rewrite mline_rel_sym.
Qed.

Lemma mtotal_rel_irrefl (G : mgraph) : irreflexive (@mtotal_rel G).
Proof. by move=> [x|e] /=; [rewrite skeleton.sk_rel_irrefl | rewrite mline_rel_irrefl]. Qed.

(** The total graph of the multigraph [G]. *)
Definition mtotal_graph (G : mgraph) : sgraph :=
  SGraph (@mtotal_rel_sym G) (@mtotal_rel_irrefl G).

(** The total chromatic number of [G]. *)
Definition mtotal_chromatic_number (G : mgraph) : nat := χ([set: mtotal_graph G]).

(** [G] is an [r]-graph: it is [r]-regular, and each odd cut has at least [r] edges. *)
Definition r_graph (G : mgraph) (r : nat) : Prop :=
  mregular G r /\ (forall X : {set G}, odd #|X| -> r <= #|mcut X|).

(** The overfull parameter of [G]: the maximum of [|E(S)| / floor(|S| / 2)], rounded up, for the
    sets [S] of vertices (those with at most one vertex count for 0). *)
Definition overfull_parameter (G : mgraph) : nat :=
  \max_(S : {set G}) ceil_div #|edge_set S| (#|S| %/ 2).

(** [G] has no loop and no parallel edges. *)
Definition msimple (G : mgraph) : Prop :=
  mloopless G /\ injective (fun e : edge G => [set source e; target e]).

(** The set [B] of blocks, on the set [T] of points, is a Steiner triple system: its blocks have
    three points, and two points are in exactly one block. *)
Definition steiner_triple_system (T : finType) (B : {set {set T}}) : Prop :=
  hg_uniform B 3 /\
  forall p q : T, p != q ->
    exists b : {set T},
      [/\ b \in B, p \in b, q \in b
        & forall b' : {set T}, b' \in B -> p \in b' -> q \in b' -> b' = b].

(** [G] is edge-colourable by the Steiner triple system [B]: the edges receive points such that
    the set of those around each vertex is a block ([G] is cubic and loopless). *)
Definition steiner_edge_colorable (G : mgraph) (T : finType) (B : {set {set T}}) : Prop :=
  exists c : edge G -> T, forall v : G, [set c e | e in edges_at v] \in B.

(** ** Colourings as maps, and the chromatic number *)

Lemma proper_coloringP (G : sgraph) (C : finType) (col : G -> C) :
  reflect (forall x y : G, x -- y -> col x != col y) (proper_coloring col).
Proof.
rewrite /proper_coloring /coloring preim_partitionP /=.
apply: (iffP forall_inP) => [stab x y|neq_col _ /imsetP[x _ ->]].
- apply: contraTN => /eqP eq_xy.
  have /stab/stableP : [set z in [set: G] | col x == col z] \in preim_partition col [set: G].
    by apply/imsetP; exists x.
  by apply; rewrite !inE ?eq_xy /=.
- apply/stableP => y z; rewrite !inE /= => /eqP eq_xy /eqP eq_xz.
  by apply/negP => /neq_col; rewrite -eq_xy -eq_xz eqxx.
Qed.

(** [G] is [k]-colourable iff its chromatic number is at most [k]. *)
Lemma chi_leP (G : sgraph) (k : nat) :
  χ([set: G]) <= k <-> exists col : G -> 'I_k, proper_coloring col.
Proof.
split=> [|[col]].
- case: chiP => P /andP[partP /forall_inP/= stabP] _ le_Pk.
  have inC x : x \in cover P by rewrite (cover_partition partP).
  have inP x : pblock P x \in enum P by rewrite mem_enum pblock_mem.
  have lt_k x : index (pblock P x) (enum P) < k.
    by rewrite (leq_trans _ le_Pk) // cardE index_mem.
  exists (fun x => Ordinal (lt_k x)); apply/proper_coloringP => x y.
  apply: contraTN => /eqP[] /(index_inj set0 (inP x) (inP y)) eq_xy.
  have /stabP/stableP : pblock P x \in P by rewrite pblock_mem.
  by apply; rewrite ?mem_pblock // eq_xy mem_pblock.
- move=> /color_bound/leq_trans; apply; rewrite -[leqRHS]card_ord.
  pose fiber (c : 'I_k) := [set y in [set: G] | c == col y].
  have -> : preim_partition col [set: G] = fiber @: (col @: [set: G]) by rewrite -imset_comp.
  exact: leq_trans (leq_imset_card _ _) (max_card _).
Qed.
