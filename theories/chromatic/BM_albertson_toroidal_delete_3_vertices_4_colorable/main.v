(** * Albertson's conjecture on toroidal graphs

Albertson; Bondy, Murty, "Graph Theory", Appendix A, problem 53.

A toroidal graph is a graph that can be embedded on the torus.

Conjecture: every toroidal graph has three vertices whose deletion leaves a 4-colourable graph.

Encoding.  Graphs are finite, simple and connected.  Connectivity is not a restriction, by the Four
Colour Theorem: at most one component of a toroidal graph is not planar.  Three vertices means at
most three, so that graphs with fewer vertices are covered.  A connected graph is toroidal if it has
an embedding in an orientable surface of genus at most 1.  Embeddings are rotation systems, and the
genus is given by Euler's formula for connected graphs. *)

From GraphTheory Require Import digraph sgraph coloring.
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

(** The number of faces of the rotation system [p]. *)
Definition face_count (p : {perm dart}) : nat := #|porbits (p * edge_perm)%g|.

(** The genus of the surface, by Euler's formula ([G] is connected). *)
Definition embedding_genus (E : embedding) : nat :=
  (2 + #|E(G)| - #|G| - face_count (rotation E)) %/ 2.

(** [G] has an embedding in the orientable surface of genus [g] ([G] is connected). *)
Definition embeds_in_genus (g : nat) : Prop := exists E : embedding, embedding_genus E <= g.

End Embedding.

(** [G] has an embedding in the torus ([G] is connected). *)
Definition toroidal (G : sgraph) : Prop := embeds_in_genus G 1.

(** ** Statement *)

Definition BM_albertson_toroidal_delete_3_vertices_4_colorable : Prop :=
  forall G : sgraph,
    toroidal G -> connected [set: G] ->
    exists S : {set G}, #|S| <= 3 /\ χ([set: G] :\: S) <= 4.
