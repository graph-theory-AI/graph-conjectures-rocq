(** * Feedback vertex sets and face packings of planar graphs

Bonamy, Dross, Masařík, Nadara, Pilipczuk, Pilipczuk, "Jones' Conjecture in subcubic graphs",
arXiv:1912.01570, Conjecture 2 (1912.01570__00).

A feedback vertex set of a graph G is a set of vertices that meets all cycles, and fvs(G) is the
minimum size of a feedback vertex set.  A cycle packing is a set of vertex-disjoint cycles.  A
face packing of a planar graph G is a cycle packing such that, for some embedding of G in the
plane, every cycle of the packing bounds a face.  The maximum size of a face packing is fp(G).

Conjecture 2: for every planar graph G, fvs(G) <= 2 fp(G).

Encoding.  Graphs are simple and connected, while the source considers all planar multigraphs.
This is no restriction: a multigraph can be made simple by subdividing its edges, which changes
neither fvs nor fp, and both are additive over the components (as a face packing never uses all
faces of a connected graph, an unused face can be taken as outer face and the components can be
drawn side by side).  Embeddings in the plane are rotation systems of genus 0, where the genus is
given by Euler's formula for connected graphs.  A cycle is given by the sequence of its vertices,
at least 3.  It bounds a face if it is the sequence of the vertices along the face, from some
starting point and in the direction given by the embedding (a cycle can be listed
in either direction, so this does not matter for packings). *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** ** Definitions copied from GraphLib/packing.v *)

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

(** The number of faces of the rotation system [p]. *)
Definition face_count (p : {perm dart}) : nat := #|porbits (p * edge_perm)%g|.

(** The genus of the surface, by Euler's formula ([G] is connected). *)
Definition embedding_genus (E : embedding) : nat :=
  (2 + #|E(G)| - #|G| - face_count (rotation E)) %/ 2.

(** The surface is the sphere. *)
Definition planar_embedding (E : embedding) : Prop := embedding_genus E = 0.

(** The vertices along the face containing [d], starting with the tail of [d]. *)
Definition face_walk (E : embedding) (d : dart) : seq G :=
  [seq (sval x).1 | x <- fingraph.orbit (face_perm E) d].

End Embedding.

(** ** Definitions specific to the conjecture *)

Section Faces.
Variable G : sgraph.
Implicit Types (E : embedding G) (d : dart G) (c : seq G) (cs : seq (seq G)).

(** [c] bounds a face of [E]. *)
Definition bounds_face E c : Prop := exists d : dart G, face_walk E d = c.

(** [cs] is a list of vertex-disjoint cycles that bound faces of [E]. *)
Definition face_packing E cs : Prop :=
  cycle_packing cs /\ (forall c, c \in cs -> bounds_face E c).

(** [G] has an embedding in the plane ([G] is connected). *)
Definition planar_graph : Prop := exists E : embedding G, planar_embedding E.

(** The maximum size of a face packing, over all embeddings of [G] in the plane, is [m]. *)
Definition face_packing_number (m : nat) : Prop :=
  (exists E : embedding G, planar_embedding E /\
     exists cs, face_packing E cs /\ size cs = m) /\
  (forall (E : embedding G) cs, planar_embedding E -> face_packing E cs -> size cs <= m).

End Faces.

(** ** Statement *)

Definition AX_planar_fvs_face_packing_ratio_2 : Prop :=
  forall (G : sgraph) (fvs fp : nat),
    connected [set: G] -> planar_graph G ->
    feedback_vertex_number G fvs -> face_packing_number G fp ->
    fvs <= 2 * fp.
