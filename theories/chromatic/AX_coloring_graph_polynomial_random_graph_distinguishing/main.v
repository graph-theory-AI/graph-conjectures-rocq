(** * Generalised chromatic polynomials of random graphs

Hogan, Scott, Tamitegama, Tan, "A note on graphs of k-colourings", arXiv:2402.04237, Problem 12
(2402.04237__01).

The k-colouring graph C_k(G) has the proper colourings of G with colours in [k] as vertices, two of
them being adjacent if they differ at exactly one vertex of G.  For a graph H, the generalised
chromatic polynomial π_G^(H)(k) is the number of sets of vertices of C_k(G) that induce a subgraph
isomorphic to H.  It is a polynomial in k.  The random graph G(n,1/2) has n vertices, and each pair
is an edge independently with probability 1/2.

Problem 12: is there a finite set of graphs H_1,...,H_t such that, for almost every G in G(n,1/2),
if π_G'^(H_i) = π_G^(H_i) for all i then G' is isomorphic to G?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The random graph is given by its edge set on {0,...,n-1}.
"Almost every" means that the probability tends to 1.  The graph G' is on {0,...,n-1} too.  This is
equivalent, as K_1 may be added to the family and π_G^(K_1) is the chromatic polynomial, of degree
n.  The polynomials are compared at k = 0,...,n max_i |H_i|, which is enough as their degrees are at
most n max_i |H_i|. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

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

(** ** Definitions copied from GraphLib/random.v *)

(** The probability that the edge set of the random graph [G(n,p)] on [0, ..., n-1] satisfies
    [P]. *)
Definition gnp_probability (R : realFieldType) (p : R) (n : nat) (P : pred {set {set 'I_n}}) : R :=
  (\sum_(E : {set {set 'I_n}} | (E \subset E('K_n)) && P E)
    p ^+ #|E| * (1 - p) ^+ (#|E('K_n)| - #|E|))%R.

(** The edge set of the random graph [G(n,p)] satisfies [P n] with high probability. *)
Definition gnp_whp (R : realFieldType) (p : R) (P : forall n : nat, pred {set {set 'I_n}}) : Prop :=
  forall eps : R, (0 < eps)%R -> eventually (fun n => (1 - eps <= gnp_probability p (P n))%R).

(** ** Definitions specific to the conjecture *)

(** π_G^(H)(k): the number of sets [S] of proper colourings of [G] with [k] colours that are the
    image of an injective map [f] from [H] such that [x] and [y] are adjacent in [H] if and only if
    [f x] and [f y] differ at exactly one vertex. *)
Definition gen_chromatic_poly (G H : sgraph) (k : nat) : nat :=
  #|[set S : {set {ffun G -> 'I_k}} |
      [forall c in S, [forall x : G, [forall y : G, (x -- y) ==> (c x != c y)]]] &&
      [exists f : {ffun H -> {ffun G -> 'I_k}},
         [&& injectiveb f, S == [set f x | x : H] &
             [forall x : H, [forall y : H,
               (x -- y) == (#|[set v : G | f x v != f y v]| == 1)]]]]]|.

(** The graphs on [{0, ..., n-1}] with edge sets [E'] and [E] are isomorphic. *)
Definition labelled_isob (n : nat) (E' E : {set {set 'I_n}}) : bool :=
  [exists f : {ffun 'I_n -> 'I_n}, injectiveb f &&
    [forall x : 'I_n, [forall y : 'I_n,
      @edge_rel (sgraph_of_edges E') x y == @edge_rel (sgraph_of_edges E) (f x) (f y)]]].

(** ** Statement *)

Definition AX_coloring_graph_polynomial_random_graph_distinguishing : Prop :=
  exists (t : nat) (Hs : 'I_t -> sgraph),
    gnp_whp (1 / 2 : rat)%R
      (fun n (E : {set {set 'I_n}}) => [forall E' : {set {set 'I_n}},
         [forall i : 'I_t, [forall k : 'I_(n * \max_(j < t) #|Hs j|).+1,
            gen_chromatic_poly (sgraph_of_edges E') (Hs i) k
              == gen_chromatic_poly (sgraph_of_edges E) (Hs i) k]]
         ==> labelled_isob E' E]).
