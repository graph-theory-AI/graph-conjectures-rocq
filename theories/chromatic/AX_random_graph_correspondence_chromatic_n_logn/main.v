(** * Correspondence chromatic number of random graphs

Dvořák, Yepremyan, "Correspondence coloring of random graphs", arXiv:2307.15048, Conjecture 1.4
(2307.15048__00).

A k-correspondence assignment for a graph G gives to each edge uv a partial matching between
{u} x [k] and {v} x [k].  A colouring for this assignment is a map φ from the vertices to [k] such
that (u,φ(u)) and (v,φ(v)) are not matched, for every edge uv.  The correspondence chromatic number
of G is the least k such that G has a colouring for every k-correspondence assignment.  The random
graph G(n,p) has n vertices, and each pair is an edge independently with probability p.

Conjecture 1.4: for every fixed positive p <= 1, the random graph G(n,1-p) has asymptotically almost
surely correspondence chromatic number Θ(n / log n).

Encoding.  The case p = 1 is excluded: the edgeless graph G(n,0) has correspondence chromatic number
1, so the conjecture fails for it.  The probability p is rational, with 0 < p < 1.  This loses
nothing, since deleting edges does not increase the correspondence chromatic number, so that the
bounds for a real p follow from those for rationals on both sides of p.  The random graph is given
by its edge set on {0,...,n-1}.  The bounds are n <= c1 k log n for every k such that G is
correspondence k-colourable, and k log n <= c2 n for some such k, where c1, c2 > 0 depend only on p,
and log n is the integer part of the binary logarithm.  The ranges of the bounded quantifiers on k
are not a restriction when n >= 2. *)

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

(** [G] is correspondence [k]-colourable, as a boolean.  In an assignment [C], the pair
    [((u, a), (v, b))] means that the colour [a] of [u] is matched to the colour [b] of [v].  For
    each edge, [C] is symmetric and is a partial matching. *)
Definition correspondence_colourableb (G : sgraph) (k : nat) : bool :=
  [forall C : {set (G * 'I_k) * (G * 'I_k)},
    [&& [forall u : G, [forall v : G, (u -- v) ==> [forall a : 'I_k, [forall b : 'I_k,
           (((u, a), (v, b)) \in C) == (((v, b), (u, a)) \in C)]]]],
        [forall u : G, [forall v : G, (u -- v) ==>
          [forall a : 'I_k, [forall b1 : 'I_k, [forall b2 : 'I_k,
           ((((u, a), (v, b1)) \in C) && (((u, a), (v, b2)) \in C)) ==> (b1 == b2)]]]]] &
        [forall u : G, [forall v : G, (u -- v) ==>
          [forall a1 : 'I_k, [forall a2 : 'I_k, [forall b : 'I_k,
           ((((u, a1), (v, b)) \in C) && (((u, a2), (v, b)) \in C)) ==> (a1 == a2)]]]]]]
    ==> [exists col : {ffun G -> 'I_k}, [forall u : G, [forall v : G,
          (u -- v) ==> (((u, col u), (v, col v)) \notin C)]]]].

(** The correspondence chromatic number [k] of the graph on [{0, ..., n-1}] with edge set [E]
    satisfies [n <= c1 * k * log n] and [k * log n <= c2 * n]. *)
Definition correspondence_number_bounds (c1 c2 n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := sgraph_of_edges E in
  [forall k : 'I_n.+1, correspondence_colourableb G k ==> (n <= c1 * k * trunc_log 2 n)] &&
  [exists k : 'I_(c2 * n).+1, correspondence_colourableb G k && (k * trunc_log 2 n <= c2 * n)].

(** ** Statement *)

Definition AX_random_graph_correspondence_chromatic_n_logn : Prop :=
  forall p : rat, (0 < p < 1)%R ->
    exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
      gnp_whp (1 - p)%R
        (fun n (E : {set {set 'I_n}}) => correspondence_number_bounds c1 c2 E)].
