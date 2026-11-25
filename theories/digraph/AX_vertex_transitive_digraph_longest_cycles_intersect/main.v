(** * Longest directed cycles in vertex-transitive digraphs

Bucić, Hendrey, Mohar, Steiner, Yepremyan, "Long cycles in vertex transitive digraphs",
arXiv:2602.16333, Question 4.3 (2602.16333__02).

A digraph is vertex-transitive if its automorphism group acts transitively on its vertices, and
connected if its underlying undirected graph is connected (which is equivalent to strong
connectivity for vertex-transitive digraphs).  Two cycles intersect if they share a vertex.

Question 4.3: is it true that in any connected vertex-transitive digraph, any two longest directed
cycles intersect?  The proposition states the positive answer.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, as in the paper.  Loops are allowed too, which is equivalent: a
connected vertex-transitive digraph with at least two vertices has a directed cycle of length at
least two.  Directed cycles are sequences of distinct vertices. *)

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

(** [c] is a directed cycle of maximum length. *)
Definition longest_dicycle (D : diGraph) (c : seq D) : Prop :=
  dicycle c /\ forall d : seq D, dicycle d -> (size d <= size c)%N.

(** The automorphisms of [D]. *)
Definition automorphisms (D : diGraph) : {set {perm D}} :=
  [set p : {perm D} | [forall u : D, [forall v : D, (p u -- p v) == (u -- v)]]].

(** [D] is vertex-transitive. *)
Definition vertex_transitive (D : diGraph) : bool :=
  [forall u : D, [forall v : D, [exists p : {perm D}, (p \in automorphisms D) && (p u == v)]]].

(** ** Statement *)

Definition AX_vertex_transitive_digraph_longest_cycles_intersect : Prop :=
  forall D : diGraph, connected [set: underlying D] -> vertex_transitive D ->
    forall c1 c2 : seq D, longest_dicycle c1 -> longest_dicycle c2 ->
      exists v : D, v \in c1 /\ v \in c2.
