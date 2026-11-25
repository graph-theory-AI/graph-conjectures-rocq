(** * The circular embedding conjecture

Haggard, "Edmonds characterization of disc embeddings", Proc. 8th Southeastern Conf. on
Combinatorics, Graph Theory and Computing, 1977; Open Problem Garden,
the_circular_embedding_conjecture.

Conjecture: every 2-connected graph has an embedding in a surface such that the boundary of each
face is a cycle.

Encoding.  Graphs are finite and simple; loopless multigraphs reduce to this case by subdividing
edges.  A 2-connected graph has at least three vertices.  Surfaces are orientable or not.  The
(cellular) embeddings are given by rotation systems with a signature: a cyclic order of the darts
(oriented edges) leaving each vertex, and a boolean for each edge, which says whether it reverses
the orientation.  The faces are the orbits of a permutation of the pairs of a dart and a local
orientation.  As degrees are at least 2, the boundary of a face is a cycle if and only if the face
does not meet a vertex twice. *)

From GraphTheory Require Import digraph sgraph connectivity.
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

End Embedding.

Section SignedEmbedding.
Variable G : sgraph.

(** Rotation systems with a signature: [signature d] means that the edge of [d] reverses the
    orientation. *)
Record signed_embedding := SignedEmb {
  unsigned_embedding : embedding G;
  signature : dart G -> bool;
  signature_edge : forall d : dart G, signature (edge_perm G d) = signature d }.

(** The rotation, in the direction [s]. *)
Definition rotation_dir (M : signed_embedding) (s : bool) : {perm dart G} :=
  if s then rotation (unsigned_embedding M) else ((rotation (unsigned_embedding M))^-1)%g.

(** The next dart on a face, with its local orientation. *)
Definition signed_face_next (M : signed_embedding) (x : dart G * bool) : dart G * bool :=
  let y := rotation_dir M x.2 x.1 in (edge_perm G y, x.2 (+) signature M y).

Lemma signed_face_next_inj (M : signed_embedding) : injective (signed_face_next M).
Proof.
move=> [d1 s1] [d2 s2]; rewrite /signed_face_next /=.
case=> /perm_inj Ey Es.
have Es12 : s1 = s2 by move: Es; rewrite Ey => /addIb.
apply/eqP; rewrite xpair_eqE; apply/andP; split; apply/eqP => //.
move: Ey; rewrite /rotation_dir Es12; case: (s2) => /perm_inj //.
Qed.

(** The permutation of the darts with orientation whose orbits are the faces (each face appears
    twice, once for each direction). *)
Definition signed_face_perm (M : signed_embedding) : {perm (dart G * bool)%type} :=
  perm (@signed_face_next_inj M).

(** The boundary of each face is a cycle: no face meets a vertex twice (if [G] has no vertex of
    degree 1). *)
Definition circular_embedding (M : signed_embedding) : Prop :=
  forall x : dart G * bool,
    {in porbit (signed_face_perm M) x &, injective (fun y : dart G * bool => (sval y.1).1)}.

End SignedEmbedding.

(** ** Statement *)

Definition OPG_2_connected_circular_surface_embedding : Prop :=
  forall G : sgraph,
    2.-connected G -> exists M : signed_embedding G, circular_embedding M.
