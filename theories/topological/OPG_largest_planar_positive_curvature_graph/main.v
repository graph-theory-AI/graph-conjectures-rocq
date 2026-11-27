(** * The largest planar graph of positive curvature

DeVos, Mohar; Open Problem Garden, what_is_the_largest_graph_of_positive_curvature.

In a graph G embedded in the sphere, the combinatorial curvature of a vertex v is
1 - deg(v)/2 + Σ_f 1/size(f), where f ranges over the faces around v.  The prism with 2n vertices
consists of two cycles of length n and a perfect matching between corresponding vertices.  The
antiprism with 2n vertices consists of two cycles of length n joined by a cycle of length 2n.

Problem: what is the largest connected planar graph of minimum degree (at least) 3 that has positive
combinatorial curvature at each vertex, but is neither a prism nor an antiprism?

The proposition states that the maximum number of vertices of such a graph is 208, the value given
by Nicholson and Sneddon (2011) and Ghidelli (arXiv:1708.08502).

Encoding.  Graphs are finite and simple.  Embeddings are given by rotation systems: a cyclic order
of the darts (oriented edges) leaving each vertex.  The faces are the orbits of a permutation of the
darts, and the surface is the sphere if the genus given by Euler's formula is 0.  The curvature is
a rational number, where a face that meets v several times is counted as many times.  Prisms and
antiprisms are excluded as graphs, up to isomorphism. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra fingroup perm.

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

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

End Products.

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

End Embedding.

Section Antiprism.
Variable n : nat.

(** The edges of the antiprism, in one direction. *)
Definition antiprism_rel (u v : 'I_n * bool) : bool :=
  let: (i, a) := u in let: (j, b) := v in
  ((a == b) && @edge_rel (cycle_graph n) i j)
  || (a && ~~ b && ((i == j) || (((val i).+1 %% n) == val j))).

(** The antiprism with [2n] vertices: two cycles of length [n] joined by a cycle of length
    [2n] ([3 <= n] is meant). *)
Definition antiprism : sgraph := sgraph_of_rel antiprism_rel.

End Antiprism.

(** [G] is a prism: the cartesian product of a cycle and an edge. *)
Definition is_prism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ cartesian_product (cycle_graph n) 'K_2).

(** [G] is an antiprism. *)
Definition is_antiprism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ antiprism n).

(** ** Definitions copied from GraphLib/geometric.v *)

Section Curvature.
Variable G : sgraph.

(** The combinatorial curvature at [v]: [1 - deg v / 2 + sum of 1 / |f|], where [f] ranges over
    the faces around [v]. *)
Definition combinatorial_curvature (E : embedding G) (v : G) : rat :=
  (1 - (#|darts_at v|)%:R / 2%:R + \sum_(d in darts_at v) 1 / (face_size E d)%:R)%R.

(** The combinatorial curvature is positive at each vertex. *)
Definition positive_curvature (E : embedding G) : Prop :=
  forall v : G, (0 < combinatorial_curvature E v)%R.

End Curvature.

(** ** Definitions specific to the conjecture *)

(** [G] is connected, has minimum degree at least 3 and an embedding in the sphere with positive
    curvature at each vertex, and is neither a prism nor an antiprism. *)
Definition sporadic_positive_curvature (G : sgraph) : Prop :=
  [/\ connected [set: G],
      forall v : G, 3 <= #|N(v)|,
      exists E : embedding G, planar_embedding E /\ positive_curvature E,
      ~ is_prism G &
      ~ is_antiprism G].

(** ** Statement *)

Definition OPG_largest_planar_positive_curvature_graph : Prop :=
  (forall G : sgraph, sporadic_positive_curvature G -> #|G| <= 208) /\
  (exists G : sgraph, sporadic_positive_curvature G /\ #|G| = 208).
