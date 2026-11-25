(** * Hypergraphs

A hypergraph on a finite type [T] of vertices is given by the set [E : {set {set T}}] of its
edges (no repeated edges; empty edges and edges with one vertex are allowed). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Hypergraph.
Variable T : finType.
Implicit Types (E M F : {set {set T}}) (e S X : {set T}) (v : T).

(** ** Edges and degrees *)

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

(** Every edge has at least two vertices. *)
Definition hg_loopless E : Prop := forall e, e \in E -> 2 <= #|e|.

(** [E] is linear: distinct edges have at most one common vertex. *)
Definition hg_linear E : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e != f -> #|e :&: f| <= 1.

(** [E] is [k]-partite and [k]-uniform for the partition given by [part]: every edge has exactly
    one vertex in each part. *)
Definition hg_partite_uniform (k : nat) (part : T -> 'I_k) E : Prop :=
  forall e, e \in E -> forall j : 'I_k, #|[set v in e | part v == j]| = 1.

(** The edges contained in [S]. *)
Definition hg_restrict E S : {set {set T}} := [set e in E | e \subset S].

(** The [i]-skeleton: the subsets with [i + 1] vertices of the edges. *)
Definition hg_skeleton E (i : nat) : {set {set T}} :=
  [set f : {set T} | (#|f| == i.+1) && [exists e in E, f \subset e]].

(** [E] is [d]-degenerate: each nonempty set [S] has a vertex that belongs to at most [d] edges
    contained in [S]. *)
Definition hg_degenerate E (d : nat) : bool :=
  [forall S : {set T}, (S != set0) ==> [exists v in S, incidence_degree (hg_restrict E S) v <= d]].

Lemma hg_degenerate_ex E : exists d, hg_degenerate E d.
Proof.
exists #|E|; apply/forallP=> S; apply/implyP=> /set0Pn[v vS]; apply/existsP; exists v; rewrite vS.
by apply/subset_leq_card/subsetP=> e; rewrite !inE => /andP[/andP[]].
Qed.

(** The degeneracy of [E]. *)
Definition hg_degeneracy E : nat := ex_minn (hg_degenerate_ex E).

(** [E] is closed under union. *)
Definition union_closed E : Prop :=
  forall A B : {set T}, A \in E -> B \in E -> (A :|: B) \in E.

(** ** Connectivity and cycles *)

(** [u] and [v] are in a common edge. *)
Definition hg_adjacent E : rel T := fun u v => [exists e in E, (u \in e) && (v \in e)].

(** Any two vertices are joined by a walk (isolated vertices matter). *)
Definition hg_connected E : Prop := forall u v : T, connect (hg_adjacent E) u v.

(** Any two vertices of [S] are joined by a walk in the edges contained in [S]. *)
Definition hg_connected_on E S : Prop :=
  forall u v : T, u \in S -> v \in S -> connect (hg_adjacent (hg_restrict E S)) u v.

(** The 2-section of [E]: two vertices are adjacent if they are in a common edge. *)
Definition two_section E : sgraph := sgraph_of_rel (hg_adjacent E).

(** [E] has a Berge cycle: distinct vertices [vs] and distinct edges [es], as many as vertices
    and at least two, such that each vertex is in the corresponding edge and in the next one
    (cyclically). *)
Definition berge_cycle E : Prop :=
  exists (vs : seq T) (es : seq {set T}),
    [/\ 2 <= size es,
        size vs = size es,
        uniq vs && uniq es,
        (forall e : {set T}, e \in es -> e \in E)
      & all (fun t : T * ({set T} * {set T}) =>
               let: (v, ef) := t in (v \in ef.1) && (v \in ef.2))
            (zip vs (zip es (rot 1 es)))].

(** [E] has no Berge cycle. *)
Definition berge_acyclic E : Prop := ~ berge_cycle E.

(** ** Matchings and covers *)

(** [M] is a matching: a set of pairwise disjoint edges. *)
Definition hg_matching M E : Prop :=
  M \subset E /\ trivIset M.

(** The matching number (maximum number of edges of a matching) of [E] is [nu]. *)
Definition hg_matching_number E (nu : nat) : Prop :=
  (exists M : {set {set T}}, hg_matching M E /\ #|M| = nu) /\
  (forall M : {set {set T}}, hg_matching M E -> #|M| <= nu).

(** [X] is a vertex cover (transversal): it meets all edges. *)
Definition hg_cover X E : Prop :=
  forall e : {set T}, e \in E -> X :&: e != set0.

(** The vertex cover number (minimum size of a vertex cover) of [E] is [tau]. *)
Definition hg_cover_number E (tau : nat) : Prop :=
  (exists X : {set T}, hg_cover X E /\ #|X| = tau) /\
  (forall X : {set T}, hg_cover X E -> tau <= #|X|).

(** ** Colourings *)

(** [col] is a proper (weak) colouring: no edge is monochromatic. *)
Definition hg_proper_coloring (C : finType) E (col : T -> C) : Prop :=
  forall e, e \in E -> exists x y, [/\ x \in e, y \in e & col x != col y].

(** [E] has a proper colouring with [m] colours. *)
Definition hg_colorable E (m : nat) : Prop :=
  exists col : T -> 'I_m, hg_proper_coloring E col.

(** ** Clique minors *)

(** The branch sets [B] of a minor [K_t]: they are nonempty, pairwise disjoint and induce
    connected hypergraphs and, for any two of them, some edge meets both and is contained in
    their union. *)
Definition hg_clique_minor_model E (t : nat) (B : 'I_t -> {set T}) : Prop :=
  [/\ forall h, B h != set0,
      forall h h', h != h' -> [disjoint B h & B h'],
      forall h, hg_connected_on E (B h) &
      forall h h' : 'I_t, h != h' ->
        exists e, [/\ e \in E, e \subset B h :|: B h',
                      e :&: B h != set0 & e :&: B h' != set0]].

(** [E] has a minor [K_t]. *)
Definition hg_has_clique_minor E (t : nat) : Prop :=
  exists B : 'I_t -> {set T}, hg_clique_minor_model E B.

End Hypergraph.

(** ** Turán numbers *)

(** [E] contains a copy of [F]. *)
Definition hg_contains (S T : finType) (F : {set {set S}}) (E : {set {set T}}) : bool :=
  [exists f : {ffun S -> T},
     injectiveb f && [forall e in F, [set f x | x in e] \in E]].

(** The Turán number of [F]: the maximum number of edges of a [k]-uniform hypergraph on [n]
    vertices without any copy of [F]. *)
Definition hg_turan_number (S : finType) (F : {set {set S}}) (k n : nat) : nat :=
  \max_(E : {set {set 'I_n}} | [forall e in E, #|e| == k] && ~~ hg_contains F E) #|E|.

(** ** Latin squares *)

(** [L] is a Latin square of order [d]: the rows and columns are permutations. *)
Definition latin_square (d : nat) (L : 'I_d -> 'I_d -> 'I_d) : Prop :=
  (forall i : 'I_d, injective (L i)) /\ (forall j : 'I_d, injective (fun i => L i j)).
