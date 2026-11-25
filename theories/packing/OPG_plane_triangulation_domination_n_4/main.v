(** * Domination in plane triangulations

Matheson, Tarjan, "Dominating sets in planar graphs", European J. Combin. 17 (1996); Open Problem
Garden, domination_in_plane_triangulations.

A set D of vertices of a graph G is dominating if every vertex is in D or has a neighbour in D.
A plane triangulation is a graph embedded in the plane so that all faces are triangles.

Conjecture: every sufficiently large plane triangulation G has a dominating set of size at most
|V(G)|/4.

Encoding.  Graphs are finite, simple and connected.  The embeddings are given by rotation systems: a
cyclic order of the darts (oriented edges) leaving each vertex.  The faces are the orbits of the
permutation [face_perm E] of the darts, and G is a triangulation if all faces have three darts.  The
embedding is in the plane (or the sphere) if the genus given by Euler's formula is 0. *)

From GraphTheory Require Import digraph sgraph.
From GraphTheory Require dom.
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

(** The number of faces of the rotation system [p]. *)
Definition face_count (p : {perm dart}) : nat := #|porbits (p * edge_perm)%g|.

(** The genus of the surface, by Euler's formula ([G] is connected). *)
Definition embedding_genus (E : embedding) : nat :=
  (2 + #|E(G)| - #|G| - face_count (rotation E)) %/ 2.

(** The surface is the sphere. *)
Definition planar_embedding (E : embedding) : Prop := embedding_genus E = 0.

(** The length of the face containing [d]. *)
Definition face_size (E : embedding) (d : dart) : nat := #|face_of E d|.

(** All faces are triangles. *)
Definition triangulation (E : embedding) : Prop := forall d : dart, face_size E d = 3.

End Embedding.

(** ** Statement *)

Definition OPG_plane_triangulation_domination_n_4 : Prop :=
  exists n0 : nat,
    forall (G : sgraph) (E : embedding G),
      connected [set: G] -> planar_embedding E -> triangulation E -> n0 <= #|G| ->
      exists D : {set G}, dom.dominating D /\ 4 * #|D| <= #|G|.
