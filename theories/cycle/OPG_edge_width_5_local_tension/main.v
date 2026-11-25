(** * 5-local-tensions

DeVos; Open Problem Garden, 5_local_tensions.  The definitions are those of DeVos, Goddyn, Mohar,
Vertigan, Zhu, "Coloring-flow duality of embedded graphs", Trans. Amer. Math. Soc. 357 (2005).

Let G be a directed graph embedded in a surface.  The height of a walk for a map φ from the edges
to the integers is the sum of φ on the forward edges of the walk minus the sum of φ on its
backward edges.  The map φ is a local-tension if the height of every contractible closed walk is
zero, and a k-local-tension if moreover 0 < |φ(e)| < k for every edge e (changing the direction of
an edge amounts to changing the sign of its value).  The edge-width of an embedded graph is the
length of its shortest non-contractible cycle.

Conjecture: there is a constant c such that every embedded loopless graph with edge-width at least
c has a 5-local-tension.

Encoding.  Graphs are finite and simple.  This is no restriction: when c >= 3, parallel edges are
homotopic, so they have the same value in a local-tension, and one of them suffices.  The surface is
any closed surface, orientable or not (one for each component of G), and the faces are assumed to be
discs.  This is also no restriction: a face that is not a disc can be replaced by discs, and then
closed walks that were contractible remain so.

An embedding is a rotation system with a signature on the edges: a cyclic order of the edges around
each vertex, and a sign that tells which edges reverse the local orientation.  Contractibility is
homotopy to a point: a closed walk is contractible if it is obtained from a walk without edges by
inserting and deleting walks around faces and walks that follow an edge and go back.  The map φ is
represented by an antisymmetric function t on ordered pairs of vertices.  The edge-width is at
least c if every cycle with fewer than c edges is contractible. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot order algebra fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

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

End SignedEmbedding.

Section EdgeWidth.
Variables (G : sgraph) (M : signed_embedding G).
Implicit Types (v x : G) (p q l : seq G).

(** The walk around the face of [a], from the vertex at [a]: its vertices, without the last one,
    which is equal to the first one. *)
Definition signed_face_walk (a : dart G * bool) : seq G :=
  [seq (sval b.1).1 | b <- fingraph.orbit (signed_face_perm M) a].

(** The closed walk [v :: p] follows an edge and goes back, or goes around a face. *)
Definition elementary_loop v p : Prop :=
  (exists2 u : G, v -- u & p = [:: u; v]) \/
  (exists a : dart G * bool, v :: p = rcons (signed_face_walk a) v).

(** The closed walk is contractible: it is obtained from a walk without edges by inserting and
    deleting elementary loops.  A walk is the list of its vertices. *)
Inductive contractible : seq G -> Prop :=
| contractible_point v : contractible [:: v]
| contractible_insert p v l q :
    elementary_loop v l -> contractible (p ++ v :: q) -> contractible (p ++ v :: l ++ q)
| contractible_delete p v l q :
    elementary_loop v l -> contractible (p ++ v :: l ++ q) -> contractible (p ++ v :: q).

(** The edge-width is at least [c]: each cycle with fewer than [c] edges is contractible. *)
Definition edge_width_ge (c : nat) : Prop :=
  forall x p, seq_cycle (--) (x :: p) -> (size p).+1 < c -> contractible (x :: rcons p x).

End EdgeWidth.

(** ** Definitions specific to the conjecture *)

Section LocalTension.
Variables (G : sgraph) (M : signed_embedding G).
Implicit Types w : seq G.

Local Open Scope ring_scope.

(** The height of the walk [w]. *)
Definition walk_height (t : G -> G -> int) w : int :=
  \sum_(a <- zip w (behead w)) t a.1 a.2.

(** [t] is a [k]-local-tension: [t x y] is the value of the edge [xy], directed from [x] to
    [y]. *)
Definition local_tension (k : nat) (t : G -> G -> int) : Prop :=
  [/\ forall x y, t y x = - t x y,
      forall x y, x -- y -> 0 < `|t x y| < k%:R
    & forall w, contractible M w -> walk_height t w = 0].

End LocalTension.

(** ** Statement *)

Definition OPG_edge_width_5_local_tension : Prop :=
  exists c : nat, forall (G : sgraph) (M : signed_embedding G),
    edge_width_ge M c -> exists t : G -> G -> int, local_tension M 5 t.
