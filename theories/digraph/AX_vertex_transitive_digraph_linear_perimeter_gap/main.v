(** * Linear perimeter gap in vertex transitive digraphs

Bucić, Hendrey, Mohar, Steiner, Yepremyan, "Long cycles in vertex transitive digraphs", 2026,
arXiv:2602.16333, Conjecture 4.1 (2602.16333__00).

A digraph is vertex transitive if its automorphism group acts transitively on its vertices, and
connected if its underlying undirected graph is connected.  The perimeter gap of a digraph is its
number of vertices minus the length of its longest directed cycle.

Conjecture: there is ε > 0 such that, for infinitely many n, there is a connected vertex transitive
digraph on n vertices whose perimeter gap is at least εn.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  Loops are allowed, which is harmless: a vertex transitive digraph has loops on all
its vertices or on none, and their deletion keeps the hypotheses and the longest cycles of length at
least 2.  We take ε = 1/m; "gap >= n/m" is written n <= m(n - |c|) for every directed cycle c, where
|c| <= n (the case m = 0 is excluded as n is arbitrarily large).  A connected vertex transitive
digraph on at least two vertices has a directed cycle. *)

From GraphTheory Require Import preliminaries sgraph digraph.
From mathcomp Require Import boot perm.

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

(** ** Definitions copied from GraphLib/digraph.v *)

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** [D] is vertex-transitive. *)
Definition vertex_transitive (D : diGraph) : bool :=
  [forall u : D, [forall v : D, [exists p : {perm D}, (p \in automorphisms D) && (p u == v)]]].

(** ** Statement *)

Definition AX_vertex_transitive_digraph_linear_perimeter_gap : Prop :=
  exists m : nat, forall N : nat, exists D : diGraph,
    [/\ N <= #|D|, connected [set: underlying D], vertex_transitive D &
        forall c : seq D, dicycle c -> #|D| <= m * (#|D| - size c)].
