(** * Grünbaum's conjecture on triangulations

Grünbaum, "Conjecture 6", in Recent Progress in Combinatorics (Tutte ed.), Academic Press, 1969,
p. 343; Open Problem Garden, grunbaums_conjecture.

Conjecture: if G is a simple loopless triangulation of an orientable surface, then the dual of G is
3-edge-colourable.

Encoding.  Graphs are finite and simple.  The embeddings in orientable surfaces are given by
rotation systems: a cyclic order of the darts (oriented edges) leaving each vertex.  The faces are
the orbits of the permutation [face_perm E] of the darts, and G is a triangulation if all faces have
three darts.  G may be disconnected, which changes nothing, as the components are triangulations.
The edges of the dual are those of G, and its vertices are the faces.  A 3-edge-colouring of the
dual is thus a colouring of the darts of G such that the two darts of an edge have the same colour,
and the three darts of a face have distinct colours. *)

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

(** Embeddings of [G]: permutations of the darts whose orbits are the sets of darts leaving a
    vertex. *)
Record embedding := Emb {
  rotation : {perm dart};
  rotation_vertex : forall d : dart, porbit rotation d = darts_at (sval d).1 }.

(** The permutation whose orbits are the faces. *)
Definition face_perm (E : embedding) : {perm dart} := (rotation E * edge_perm)%g.

(** The face containing the dart [d], as a set of darts. *)
Definition face_of (E : embedding) (d : dart) : {set dart} := porbit (face_perm E) d.

(** The length of the face containing [d]. *)
Definition face_size (E : embedding) (d : dart) : nat := #|face_of E d|.

(** All faces are triangles. *)
Definition triangulation (E : embedding) : Prop := forall d : dart, face_size E d = 3.

End Embedding.

(** ** Statement *)

Definition OPG_grunbaum_triangulation_dual_3_edge_colorable : Prop :=
  forall (G : sgraph) (E : embedding G),
    triangulation E ->
    exists c : dart G -> 'I_3,
      (forall d : dart G, c d = c (edge_perm G d)) /\
      (forall d : dart G,
         [/\ c d <> c (face_perm E d),
             c (face_perm E d) <> c (face_perm E (face_perm E d)) &
             c d <> c (face_perm E (face_perm E d))]).
