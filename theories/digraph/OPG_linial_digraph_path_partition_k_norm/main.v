(** * Linial-Berge path partition duality

Linial, "Extending the Greene-Kleitman theorem to directed graphs", J. Combin. Theory Ser. A 30
(1981); Open Problem Garden, linial_berge_path_partition_duality.

A path partition of a digraph D is a set of vertex-disjoint directed paths of D (possibly with a
single vertex) that covers all the vertices.  For a positive integer k, its k-norm is the sum of
min(|V(P)|, k) over its paths P.  An induced subgraph of D is k-colourable if its vertices can be
partitioned into k stable sets (sets without arc between two of their vertices).

Conjecture: for every digraph D and every positive integer k, the minimum k-norm of a path partition
of D is at most the maximum size (number of vertices) of a k-colourable induced subgraph of D.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and so are loops, which are ignored in paths and in colourings.
A directed path is given by its first vertex and the sequence of the other ones.  The inequality is
expressed by the existence of a path partition Q and of a set S of vertices, such that the k-norm of
Q is at most |S| and the subgraph induced by S is k-colourable ([χ(S)] is the chromatic number of
the subgraph induced by S in the underlying graph of D). *)

From GraphTheory Require Import preliminaries sgraph coloring digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** [Q] is a partition of the vertices into directed paths ([(x, s)] stands for [x :: s]). *)
Definition dipath_partition (D : diGraph) (Q : seq (D * seq D)) : bool :=
  [&& all (fun p => dipath p.1 p.2) Q,
      [forall v : D, has (fun p => v \in p.1 :: p.2) Q] &
      [forall v : D, count (fun p => v \in p.1 :: p.2) Q <= 1]].

(** The [k]-norm of a family of paths: the sum of min(k, number of vertices). *)
Definition dipath_knorm (D : diGraph) (k : nat) (Q : seq (D * seq D)) : nat :=
  \sum_(p <- Q) minn k (size (p.1 :: p.2)).

(** ** Statement *)

Definition OPG_linial_digraph_path_partition_k_norm : Prop :=
  forall (D : diGraph) (k : nat), 0 < k ->
    exists (Q : seq (D * seq D)) (S : {set underlying D}),
      [/\ dipath_partition Q, χ(S) <= k & dipath_knorm k Q <= #|S|].
