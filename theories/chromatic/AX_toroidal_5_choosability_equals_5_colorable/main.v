(** * 5-choosability of toroidal graphs

Dvořák, Moreno Peñarrubia, "Towards Characterization of 5-List-Colorability of Toroidal Graphs",
arXiv:2407.18800, Conjecture 3 (2407.18800__01).

A graph is k-choosable if it has a proper colouring from all lists of at least k colours on its
vertices.

Conjecture 3: a toroidal graph is 5-choosable if and only if it is 5-colourable.

Encoding.  Graphs are finite and simple.  A connected graph is toroidal if it has an embedding in
an orientable surface of genus at most 1 (thus planar graphs are toroidal).  Embeddings are rotation
systems, and the genus is given by Euler's formula.  Connectedness is no restriction, as the
components of a toroidal graph are toroidal. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

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

Definition AX_toroidal_5_choosability_equals_5_colorable : Prop :=
  forall G : sgraph,
    toroidal G -> connected [set: G] ->
    (choosable G 5 <-> χ([set: G]) <= 5).
