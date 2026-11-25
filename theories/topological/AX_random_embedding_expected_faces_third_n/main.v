(** * Maximum expected number of faces of a random embedding

Campion Loth, Mohar, "Expected number of faces in a random embedding of any graph is at most
linear", arXiv:2202.07746, Conjecture 4 (2202.07746__00).

An embedding means a cellular embedding in an orientable surface.  The embeddings of a connected
graph correspond to its rotation systems: a cyclic order of the edges around each vertex.  A random
embedding is given by a rotation system chosen uniformly at random.

Conjecture 4: for every (connected) simple graph G on n vertices, the expected number of faces of a
random embedding of G is at most n/3 + 1.

Encoding.  Graphs are finite and simple.  The rotation systems are the permutations of the darts
(oriented edges) whose orbits are the sets of darts leaving a vertex.  The faces are the orbits of
another permutation of the darts.  The expected number of faces is the total number of faces
of the rotation systems of G divided by their number (which is not 0).  The graph is connected, as
it must have cellular embeddings; the bound would fail for four disjoint edges.  The graph with one
vertex has no face here (instead of one); it satisfies the bound in both cases. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/topological.v *)

Section Embedding.
Variable G : sgraph.

(** The darts of [G]: the edges with an orientation. *)
Definition dart : Type := {p : G * G | p.1 -- p.2}.

Lemma rev_dart_proof (d : dart) : (sval d).2 -- (sval d).1.
Proof. by rewrite sg_sym; exact: (svalP d). Qed.

(** The opposite dart. *)
Definition rev_dart (d : dart) : dart := exist _ ((sval d).2, (sval d).1) (rev_dart_proof d).

Lemma rev_dartK : involutive rev_dart.
Proof. by move=> d; apply/val_inj; case: d => [[x y] p]. Qed.

(** The permutation that exchanges the two darts of each edge. *)
Definition edge_perm : {perm dart} := perm (inv_inj rev_dartK).

(** The darts leaving [v]. *)
Definition darts_at (v : G) : {set dart} := [set d : dart | (sval d).1 == v].

(** The number of faces of the rotation system [p]. *)
Definition face_count (p : {perm dart}) : nat := #|porbits (p * edge_perm)%g|.

(** The rotation systems of [G]: the permutations that give an embedding. *)
Definition rotation_systems : {set {perm dart}} :=
  [set p | [forall d, porbit p d == darts_at (sval d).1]].

(** The total number of faces of the rotation systems of [G]. *)
Definition total_faces : nat :=
  \sum_(p in rotation_systems) face_count p.

End Embedding.

(** ** Statement *)

Definition AX_random_embedding_expected_faces_third_n : Prop :=
  forall G : sgraph,
    connected [set: G] -> 3 * total_faces G <= (#|G| + 3) * #|rotation_systems G|.
