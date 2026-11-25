(** * Turán exponents of k-partite hypergraphs and skeletal degeneracy

Fox, Sankar, Simkin, Tidor, Zhou, "Ramsey and Turán numbers of sparse hypergraphs",
arXiv:2401.00359, Conjecture 6.2 (2401.00359__01).

A k-uniform hypergraph H is k-partite if its vertices can be partitioned into k parts such that
every edge has one vertex in each part.  The degeneracy of a hypergraph is the least d such that
each of its subhypergraphs has a vertex of degree at most d.  The i-skeleton of H is the
(i+1)-uniform hypergraph formed by the sets of i+1 vertices contained in an edge of H, and d_i(H)
is the degeneracy of the i-skeleton.  Let d_max(H) be the maximum of d_i(H) for 1 <= i < k.  The
Turán number ex(n,H) is the maximum number of edges of a k-uniform hypergraph on n vertices without
any copy of H.

Conjecture 6.2: there is a constant c_k > 0 such that ex(n,H) <= O_H(n^(k - c_k / d_max(H))) for
every k-uniform k-partite hypergraph H.

Encoding.  H has at least one edge and k >= 2, so that d_max(H) > 0.  The constant c_k can be
decreased, so it is assumed to be 1/q for a positive integer q.  The inequality is raised to the
power q d, where d = d_max(H), and multiplied by n: ex(n,H)^(q d) n <= K n^(k q d) for some
constant K that depends on H and for all large enough n. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** The number of members of [F] that contain [v]: the degree of [v] in the hypergraph [F], or
    in the spanning subgraph with edge set [F]. *)
Definition incidence_degree (T : finType) (F : {set {set T}}) (v : T) : nat :=
  #|[set e in F | v \in e]|.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}).

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

End Hypergraph.

(** [E] contains a copy of [F]. *)
Definition hg_contains (S T : finType) (F : {set {set S}}) (E : {set {set T}}) : bool :=
  [exists f : {ffun S -> T},
     injectiveb f && [forall e in F, [set f x | x in e] \in E]].

(** The Turán number of [F]: the maximum number of edges of a [k]-uniform hypergraph on [n]
    vertices without any copy of [F]. *)
Definition hg_turan_number (S : finType) (F : {set {set S}}) (k n : nat) : nat :=
  \max_(E : {set {set 'I_n}} | [forall e in E, #|e| == k] && ~~ hg_contains F E) #|E|.

(** ** Definitions specific to the conjecture *)

(** The maximum degeneracy of the [i]-skeletons of [E] for [1 <= i < k]. *)
Definition hg_dmax (T : finType) (E : {set {set T}}) (k : nat) : nat :=
  \max_(i < k | 0 < i) hg_degeneracy (hg_skeleton E i).

(** ** Statement *)

Definition AX_sparse_hypergraph_turan_exponent_max_degree : Prop :=
  forall k : nat, 2 <= k ->
    exists q : nat,
      0 < q /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 -> hg_partite_uniform part F ->
        exists K : nat,
          eventually (fun n =>
            hg_turan_number F k n ^ (q * hg_dmax F k) * n <= K * n ^ (k * (q * hg_dmax F k))).
