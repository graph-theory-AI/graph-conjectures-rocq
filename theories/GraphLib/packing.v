(** * Matchings, packings and partitions

Matchings of simple graphs ([matching M], a set of 2-element sets) are those of GraphTheory.
Cycles of simple graphs are sequences of vertices. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph coloring connectivity.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Matchings *)

(** [M] is a perfect matching. *)
Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  matching M /\ cover M = [set: G].

(** [M] is a matching of the multigraph [G] (without loops). *)
Definition mmatching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, (mdeg_in M v <= 1)%N.

(** [M] is a perfect matching of the multigraph [G] (without loops). *)
Definition mperfect_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, mdeg_in M v = 1.

(** [L] is a list of [k] perfect matchings such that each edge is in exactly two of them. *)
Definition matching_double_cover (G : mgraph) (k : nat)
    (L : seq {set edge G}) : Prop :=
  [/\ size L = k,
      (forall M, M \in L -> mperfect_matching M)
    & forall e : edge G, count (fun M : {set edge G} => e \in M) L = 2].

(** [G] has a matching cut: a partition of its vertices into two nonempty parts such that each
    vertex has at most one neighbour in the other part. *)
Definition matching_cut (G : sgraph) : Prop :=
  exists A : {set G},
    [/\ A != set0, A != [set: G]
      & forall v : G,
          (v \in A -> #|N(v) :&: (~: A)| <= 1) /\
          (v \notin A -> #|N(v) :&: A| <= 1)].

(** ** Partitions *)

(** The sets [E i] (possibly empty) form a partition of the edges of [G]. *)
Definition edge_partition (G : sgraph) (m : nat) (E : 'I_m -> {set {set G}}) : Prop :=
  (forall e : {set G}, (e \in E(G)) = [exists i : 'I_m, e \in E i]) /\
  forall i j : 'I_m, i != j -> [disjoint E i & E j].

(** The edges of [G] can be partitioned into at most [m] paths. *)
Definition path_number_le (G : sgraph) (m : nat) : Prop :=
  exists (r : nat) (P : 'I_r -> seq G),
    [/\ r <= m,
        (forall i : 'I_r, seq_simple_path (P i)),
        (forall i j : 'I_r,
            i != j ->
            [disjoint seq_edge_set (P i) & seq_edge_set (P j)])
      & \bigcup_(i : 'I_r) seq_edge_set (P i) = E(G)].

(** The partition of the vertices into [A] and its complement is friendly: both parts are
    nonempty, and each vertex has at least as many neighbours in its own part as in the other
    one. *)
Definition friendly_partition (G : sgraph) (A : {set G}) : Prop :=
  [/\ A != set0, A != [set: G]
    & forall v : G,
        (v \in A -> #|N(v) :&: (~: A)| <= #|N(v) :&: A|) /\
        (v \notin A -> #|N(v) :&: A| <= #|N(v) :&: (~: A)|)].

(** ** Packings *)

(** [G1] and [G2] pack: they have edge-disjoint copies on the same vertices. *)
Definition packs (G1 G2 : sgraph) : Prop :=
  exists f : G1 -> G2,
    bijective f /\ forall x y : G1, x -- y -> ~~ (f x -- f y).

(** [X] is a feedback vertex set: it meets all cycles. *)
Definition feedback_vertex_set (G : sgraph) (X : {set G}) : Prop :=
  forall c : seq G, seq_cycle (--) c -> exists2 v : G, v \in c & v \in X.

(** The minimum size of a feedback vertex set is [m]. *)
Definition feedback_vertex_number (G : sgraph) (m : nat) : Prop :=
  (exists X : {set G}, feedback_vertex_set X /\ #|X| = m) /\
  (forall X : {set G}, feedback_vertex_set X -> m <= #|X|).

(** [cs] is a list of vertex-disjoint cycles. *)
Definition cycle_packing (G : sgraph) (cs : seq (seq G)) : Prop :=
  (forall c : seq G, c \in cs -> seq_cycle (--) c) /\
  (forall v : G, count (fun c => v \in c) cs <= 1).

(** The maximum number of vertex-disjoint cycles is [m]. *)
Definition cycle_packing_number (G : sgraph) (m : nat) : Prop :=
  (exists cs : seq (seq G), cycle_packing cs /\ size cs = m) /\
  (forall cs : seq (seq G), cycle_packing cs -> size cs <= m).

(** ** Hitting sets of the maximum stable sets *)

(** The minimum size of a set of vertices that meets all maximum stable sets of [G] is at most
    [b]. *)
Definition stable_hitting_number_le (G : sgraph) (b : nat) : Prop :=
  exists X : {set G}, hg_cover X (maxstabsets [set: G]) /\ #|X| <= b.

(** The class [C] is η-bounded: on its graphs, the minimum size of a set of vertices that meets all
    maximum stable sets is bounded by a function of the clique number. *)
Definition eta_bounded (C : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, C G -> 0 < #|G| -> stable_hitting_number_le G (f ω(G)).

(** ** Edge-disjoint paths *)

(** [P] joins some demands (pairs of vertices) of the list [D] by edge-disjoint paths: its [i]-th
    element is a path between the ends of the [i]-th demand, or the empty list if this demand is
    not joined. *)
Definition edp_solution (G : sgraph) (D : seq (G * G)) (P : seq (seq G)) : bool :=
  [&& size P == size D,
      all (fun x : (G * G) * seq G =>
             nilp x.2 || seq_path_between [set x.1.1] [set x.1.2] x.2) (zip D P)
    & uniq (flatten [seq seq_edge_list p | p <- P])].

(** The number of demands that are joined. *)
Definition edp_value (G : sgraph) (P : seq (seq G)) : nat := count (fun p => ~~ nilp p) P.

(** The instances: a graph and a list of demands. *)
Definition edp_input : Type := {G : sgraph & seq (G * G)}.

(** The encoding of an instance. *)
Definition enc_edp (x : edp_input) : data :=
  Dpair (enc_graph (projT1 x))
        (enc_list [seq Dpair (Dnat (enum_rank d.1)) (Dnat (enum_rank d.2))
                  | d <- projT2 x]).

(** The encoding of a list of paths. *)
Definition enc_paths (G : sgraph) (P : seq (seq G)) : data :=
  enc_list [seq enc_list [seq Dnat (enum_rank v) | v <- p] | p <- P].

(** The output encodes a solution whose value is at least the optimum divided by [rho n], where
    [n] is the number of vertices. *)
Definition edp_approximation (rho : nat -> nat) (x : edp_input) (out : data) : Prop :=
  exists P : seq (seq (projT1 x)),
    [/\ out = enc_paths P,
        edp_solution (projT2 x) P
      & forall Q : seq (seq (projT1 x)),
          edp_solution (projT2 x) Q -> edp_value Q <= rho #|projT1 x| * edp_value P].

(** ** Subcubes *)

(** The subcube of the hypercube given by [c]: the coordinate [i] is fixed to [b] if
    [c i = Some b], and free if [c i = None]. *)
Definition subcube (d : nat) (c : {ffun 'I_d -> option bool}) : {set hypercube d} :=
  [set x : hypercube d | [forall i : 'I_d, oapp (fun b => tnth x i == b) true (c i)]].

(** The dimension of the subcube given by [c]. *)
Definition subcube_dim (d : nat) (c : {ffun 'I_d -> option bool}) : nat :=
  #|[set i : 'I_d | c i == None]|.

(** [S] is a subcube. *)
Definition is_subcube (d : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, S == subcube c].

(** The partitions of the hypercube into subcubes. *)
Definition subcube_partitions (d : nat) : {set {set {set hypercube d}}} :=
  [set P : {set {set hypercube d}} |
     partition P [set: hypercube d] && [forall S in P, is_subcube S]].

(** A subcube of dimension k has 2^k vertices. *)
Lemma card_subcube (d : nat) (c : {ffun 'I_d -> option bool}) : #|subcube c| = 2 ^ subcube_dim c.
Proof.
pose F i : pred bool := [pred b | oapp (eq_op b) true (c i)].
have -> : #|subcube c| = #|family F|.
  rewrite -(card_imset _ (can_inj (@finfun_of_tupleK bool d))) -[RHS]cardsE.
  apply: eq_card => f; rewrite [in RHS]inE; apply/imsetP/familyP => [[x]|fF].
    by rewrite inE => /forallP xc -> i; rewrite ffunE; apply: xc.
  exists (tuple_of_finfun f); last by rewrite tuple_of_finfunK.
  by rewrite inE; apply/forallP => i; rewrite tnth_mktuple; apply: fF.
rewrite card_family foldrE big_map big_enum /= -prod_nat_const [RHS]big_mkcond /=.
apply: eq_bigr => i _; rewrite inE /F.
case: (c i) => [b|] /=; last by rewrite -card_bool; apply: eq_card.
by rewrite -(card1 b); apply: eq_card => b'; rewrite !inE.
Qed.
