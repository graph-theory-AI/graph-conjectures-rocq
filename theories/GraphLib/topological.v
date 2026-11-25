(** * Planarity and embeddings of graphs in surfaces

Planarity is defined by excluded minors (Wagner's theorem).  Embeddings are combinatorial
maps: a rotation system gives a cyclic order of the darts (oriented edges) leaving each
vertex.  Rotation systems represent the cellular embeddings in orientable surfaces; with a
signature on the edges, they represent all cellular embeddings.  Only simple graphs without
labels are considered.  The formulas for the genus are those of connected graphs. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
From mathcomp Require Import boot order algebra fingroup perm.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Planarity *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** [G] is the union of two planar graphs on its vertices (thickness at most 2). *)
Definition biplanar (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ planar (SGraph s1 i1),
        planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].


(** [G] is planar after the deletion of some set of [k] vertices. *)
Definition planar_after_deleting (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| = k /\ planar (induced (~: S)).

(** [G] is planar after the deletion of some vertex. *)
Definition apex (G : sgraph) : Prop := planar_after_deleting G 1.

(** ** Embeddings in orientable surfaces *)

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

(** [G] has an embedding in the orientable surface of genus [g] ([G] is connected). *)
Definition embeds_in_genus (g : nat) : Prop := exists E : embedding, embedding_genus E <= g.

(** The vertices along the face containing [d], starting with the tail of [d]. *)
Definition face_walk (E : embedding) (d : dart) : seq G :=
  [seq (sval x).1 | x <- fingraph.orbit (face_perm E) d].

(** The length of the face containing [d]. *)
Definition face_size (E : embedding) (d : dart) : nat := #|face_of E d|.

(** All faces are triangles. *)
Definition triangulation (E : embedding) : Prop := forall d : dart, face_size E d = 3.

(** The combinatorial curvature at [v]: [1 - deg v / 2 + sum of 1 / |f|], where [f] ranges over
    the faces around [v]. *)
Definition combinatorial_curvature (E : embedding) (v : G) : rat :=
  (1 - (#|darts_at v|)%:R / 2%:R + \sum_(d in darts_at v) 1 / (face_size E d)%:R)%R.

(** The combinatorial curvature is positive at each vertex. *)
Definition positive_curvature (E : embedding) : Prop :=
  forall v : G, (0 < combinatorial_curvature E v)%R.

(** The rotation systems of [G]: the permutations that give an embedding. *)
Definition rotation_systems : {set {perm dart}} :=
  [set p | [forall d, porbit p d == darts_at (sval d).1]].

(** The total number of faces of the rotation systems of [G]. *)
Definition total_faces : nat :=
  \sum_(p in rotation_systems) face_count p.

End Embedding.

(** [G] has an embedding in the torus ([G] is connected). *)
Definition toroidal (G : sgraph) : Prop := embeds_in_genus G 1.

(** ** Embeddings in all surfaces *)

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

(** ** Contractible walks, edge-width *)

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

(** ** Straight-line drawings *)

Section StraightLine.
Variable R : realFieldType.
Local Open Scope ring_scope.

(** The points of the plane. *)
Definition plane_point := (R * R)%type.

(** Twice the signed area of the triangle [a b c]. *)
Definition signed_area (a b c : plane_point) : R :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1).

(** [a], [b] and [c] are on a line. *)
Definition collinear (a b c : plane_point) : Prop := signed_area a b c = 0.

(** [c] is on the segment [a b]. *)
Definition on_segment (a b c : plane_point) : Prop :=
  collinear a b c /\ (c.1 - a.1) * (c.1 - b.1) <= 0 /\ (c.2 - a.2) * (c.2 - b.2) <= 0.

(** The segments [a b] and [c d] are not on a line and cross at an interior point of both. *)
Definition segments_cross (a b c d : plane_point) : Prop :=
  ~ (0 < signed_area a b c * signed_area a b d) /\
  ~ (0 < signed_area c d a * signed_area c d b) /\
  signed_area a b c != 0 /\ signed_area a b d != 0 /\
  signed_area c d a != 0 /\ signed_area c d b != 0.

(** The segments [a b] and [c d] have a common point. *)
Definition segments_meet (a b c d : plane_point) : Prop :=
  segments_cross a b c d \/
  on_segment a b c \/ on_segment a b d \/ on_segment c d a \/ on_segment c d b.


(** [pos] is a planar straight-line drawing of [G]. *)
Definition straightline_planar (G : sgraph) (pos : G -> plane_point) : Prop :=
  [/\ injective pos,
      (forall w x y : G, x -- y -> w != x -> w != y -> ~ on_segment (pos x) (pos y) (pos w)) &
      (forall x y u v : G, x -- y -> u -- v -> [disjoint [set x; y] & [set u; v]] ->
         ~ segments_meet (pos x) (pos y) (pos u) (pos v)) ].

(** Every planar graph on [n] vertices has a planar straight-line drawing on points of [P]. *)
Definition universal_point_set (P : seq plane_point) (n : nat) : Prop :=
  forall G : sgraph, planar G -> #|G| = n ->
    exists pos : G -> plane_point, straightline_planar pos /\ (forall x : G, pos x \in P).

End StraightLine.

(** ** Queue layouts *)

(** The queue number of [G] is at most [k]: for some linear order of the vertices, the edges can
    be given [k] colours so that no edge [c d] is nested inside an edge [a b] of the same
    colour. *)
Definition queue_number_le (G : sgraph) (k : nat) : Prop :=
  exists (ord : G -> nat) (q : {set G} -> nat),
    [/\ injective ord,
        (forall e : {set G}, e \in E(G) -> q e < k) &
        forall a b c d : G,
          a -- b -> c -- d -> q [set a; b] = q [set c; d] ->
          ord a < ord c -> ord c < ord d -> ord d < ord b -> False].

(** ** Truncations, prisms and antiprisms *)

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

(** The truncation of [G]: two darts are adjacent if they leave the same vertex or if they are
    opposite. *)
Definition truncation (G : sgraph) : sgraph :=
  sgraph_of_rel (fun d e : dart G => ((sval d).1 == (sval e).1) || (e == rev_dart d)).

(** [G] is a prism: the cartesian product of a cycle and an edge. *)
Definition is_prism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ cartesian_product (cycle_graph n) 'K_2).

(** [G] is an antiprism. *)
Definition is_antiprism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ antiprism n).

(** ** Darts, rotations and faces: basic properties *)

(** The orbits of a permutation partition every set. *)
Lemma card_porbitsI (T : finType) (s : {perm T}) (A : {set T}) :
  \sum_(O in porbits s) #|O :&: A| = #|A|.
Proof.
rewrite -sum1_card (partition_big (porbit s) (mem (porbits s))) /=.
  by move=> x _; exact: imset_f.
apply: eq_bigr => _ /imsetP[x _ ->]; rewrite -sum1_card; apply: eq_bigl => y.
by rewrite inE andbC eq_porbit_mem.
Qed.

Section RotationTheory.
Variable G : sgraph.
Implicit Types (E : embedding G) (d : dart G) (v : G).

Lemma edge_permE d : edge_perm G d = rev_dart d.
Proof. exact: permE. Qed.

Lemma face_permE E d : face_perm E d = rev_dart (rotation E d).
Proof. by rewrite /face_perm permM edge_permE. Qed.

(** The darts at [v] are the iterates of one of them under the rotation. *)
Lemma rotation_traject E d (s := traject (rotation E) d #|darts_at (sval d).1|) :
  [/\ uniq s, iter #|darts_at (sval d).1| (rotation E) d = d
    & forall x, (x \in s) = ((sval x).1 == (sval d).1)].
Proof.
rewrite {}/s -(rotation_vertex E); split; [exact: uniq_traject_porbit|exact: iter_porbit|].
by move=> x; rewrite -porbit_traject rotation_vertex inE.
Qed.

Lemma rotation_tail E d : (sval (rotation E d)).1 = (sval d).1.
Proof.
by have := mem_porbit (rotation E) 1 d; rewrite rotation_vertex inE expg1 => /eqP.
Qed.

Lemma face_perm_head E d : (sval (face_perm E d)).2 = (sval d).1.
Proof. by rewrite face_permE /= rotation_tail. Qed.

Lemma card_darts_at v : #|darts_at v| = #|N(v)|.
Proof.
have inj : {in darts_at v &, injective (fun d => (sval d).2)}.
  move=> [[x y] xy] [[x' y'] xy'] /=; rewrite !inE /= => /eqP ex /eqP ex' ey.
  by apply: val_inj; rewrite /= ex ex' ey.
rewrite -(card_in_imset inj); apply: eq_card => y; rewrite inE.
apply/imsetP/idP => [[[[x z] xz]]|vy]; first by rewrite inE /= => /eqP <- ->.
by exists (exist _ (v, y) vy); rewrite ?inE.
Qed.

Lemma card_dart : #|{: dart G}| = 2 * #|E(G)|.
Proof.
rewrite edges_sum_degrees -sum1_card (partition_big (fun d : dart G => (sval d).1) xpredT) //=.
apply: eq_bigr => v _; rewrite -card_darts_at -sum1_card; apply: eq_bigl => d.
by rewrite inE.
Qed.

Lemma card_porbits_edge_perm : #|porbits (edge_perm G)| = #|E(G)|.
Proof.
apply: double_inj; rewrite -!muln2 [RHS]mulnC -card_dart -cardsT.
rewrite -(card_porbitsI (edge_perm G)) -sum_nat_const.
apply: eq_bigr => _ /imsetP[d _ ->]; rewrite setIT.
have -> : porbit (edge_perm G) d = [set d; rev_dart d].
  apply/setP => x; rewrite !inE; apply/porbitP/orP => [[i ->]|[]/eqP->].
  - rewrite permX; elim: i => [|i IH]; first by left.
    by rewrite iterS edge_permE; case: IH => /eqP ->; [right|left; rewrite rev_dartK].
  - by exists 0; rewrite expg0 perm1.
  - by exists 1; rewrite expg1 edge_permE.
rewrite cards2; case: eqP => // /(congr1 (fun x => (sval x).1)) /= dd.
by have := svalP d; rewrite /= dd sg_irrefl.
Qed.

Lemma card_porbits_rotation E : min_degree_ge G 1 -> #|porbits (rotation E)| = #|G|.
Proof.
move=> deg; have -> : porbits (rotation E) = [set darts_at v | v : G].
  apply/setP => O; apply/imsetP/imsetP => [[d _ ->]|[v _ ->]].
    by exists (sval d).1 => //; exact: rotation_vertex.
  have : 0 < #|darts_at v| by rewrite card_darts_at.
  case/card_gt0P => d dv; exists d => //; rewrite rotation_vertex.
  by move: dv; rewrite inE => /eqP ->.
rewrite card_imset // => v w vw.
have : 0 < #|darts_at v| by rewrite card_darts_at.
case/card_gt0P => d; rewrite inE => /eqP dv.
have : d \in darts_at w by rewrite -vw inE dv.
by rewrite inE dv => /eqP.
Qed.

(** The Euler characteristic is even. *)
Lemma odd_face_count E :
  min_degree_ge G 1 -> odd (face_count (rotation E)) = odd (#|G| + #|E(G)|).
Proof.
move=> deg; have := odd_permM (rotation E) (edge_perm G).
rewrite /odd_perm card_porbits_rotation // card_porbits_edge_perm card_dart.
by rewrite mul2n odd_double /= oddD.
Qed.

Lemma rotation_neq E d : 1 < #|N((sval d).1)| -> rotation E d != d.
Proof.
rewrite -card_darts_at => deg; have [+ _ _] := rotation_traject E d.
by case: #|_| deg => [|[|n]] //= _; rewrite inE negb_or eq_sym => /andP[/andP[]].
Qed.

(** Faces have length at least 3, if the degrees are at least 2. *)
Lemma face_size_ge3 E d : min_degree_ge G 2 -> 2 < face_size E d.
Proof.
move=> deg; have neq1 x : face_perm E x != x.
  apply/eqP => /(congr1 (fun y => (sval y).2)); rewrite face_perm_head => e.
  by have := svalP x; rewrite /= -e sg_irrefl.
have neq2 : face_perm E (face_perm E d) != d.
  apply: contraNneq (rotation_neq E (deg (sval d).1)) => e; apply/eqP/val_inj.
  rewrite [LHS]surjective_pairing [RHS]surjective_pairing rotation_tail; congr pair.
  by rewrite -[in RHS]e face_perm_head face_permE.
suff /subset_leq_card : [set d; face_perm E d; face_perm E (face_perm E d)]
    \subset face_of E d.
  by rewrite -setUA !cardsU1 cards1 !inE negb_or ![d == _]eq_sym neq1 neq2 eq_sym neq1.
rewrite !subUset !sub1set porbit_id; have := mem_porbit (face_perm E) 1 d.
by have := mem_porbit (face_perm E) 2 d; rewrite !permX /= => -> ->.
Qed.

End RotationTheory.

(** ** Embeddings given by lists of neighbours *)

Section ListEmbedding.
Variables (G : sgraph) (nb : G -> seq G).
Hypothesis nbP : forall v u : G, (u \in nb v) = (v -- u).
Hypothesis nbU : forall v : G, uniq (nb v).

Lemma list_rotation_proof (d : dart G) : (sval d).1 -- next (nb (sval d).1) (sval d).2.
Proof. by rewrite -nbP mem_next nbP; exact: (svalP d). Qed.

Lemma list_rotation_inj : injective
  (fun d => exist _ ((sval d).1, next (nb (sval d).1) (sval d).2) (list_rotation_proof d) : dart G).
Proof.
move=> [[v u] p] [[v' u'] p'] /(congr1 val) /= [ev]; subst v'.
by move=> /(can_inj (prev_next (nbU v))) eu; subst u'; apply: val_inj.
Qed.

Lemma list_rotation_vertex (d : dart G) : porbit (perm list_rotation_inj) d = darts_at (sval d).1.
Proof.
have iterE n : val ((perm list_rotation_inj ^+ n)%g d)
    = ((sval d).1, iter n (next (nb (sval d).1)) (sval d).2).
  rewrite permX; elim: n => [|n IH] /=; first by case: (sval d).
  by rewrite permE /= IH.
apply/setP => x; rewrite inE; apply/porbitP/eqP => [[n ->]|ex]; first by rewrite iterE.
have : fconnect (next (nb (sval d).1)) (sval d).2 (sval x).2.
  rewrite (fconnect_cycle (cycle_next (nbU _))) nbP ?(svalP d) // -ex.
  exact: (svalP x).
move=> /iter_findex ey; exists (findex (next (nb (sval d).1)) (sval d).2 (sval x).2).
by apply: val_inj; rewrite iterE ey -ex [LHS]surjective_pairing.
Qed.

(** The embedding such that [nb v] is the cyclic order of the neighbours of [v]. *)
Definition list_embedding : embedding G := Emb list_rotation_vertex.

(** Its face permutation, on pairs of vertices. *)
Definition list_face (p : G * G) : G * G := (next (nb p.1) p.2, p.1).

Lemma list_face_perm d : val (face_perm list_embedding d) = list_face (val d).
Proof. by rewrite face_permE permE. Qed.

Lemma list_face_walk d n (s := traject list_face (val d) n) :
  uniq s -> iter n list_face (val d) = val d -> 0 < n ->
  face_walk list_embedding d = [seq p.1 | p <- s].
Proof.
set f := face_perm list_embedding.
have iterE m x : val (iter m f x) = iter m list_face (val x).
  by elim: m => //= m <-; exact: list_face_perm.
have trajE m x : map val (traject f x m) = traject list_face (val x) m.
  by elim: m x => //= m IH x; rewrite IH -list_face_perm.
rewrite {}/s -trajE (map_inj_uniq val_inj) -map_comp; case: n => // n Us.
rewrite -iterE => /val_inj closed _; congr map.
have fc : fcycle f (traject f d n.+1).
  by rewrite /= rcons_path fpath_traject last_traject; apply/eqP.
by rewrite (fingraph.orbitE fc Us (mem_head _ _)) /= eqxx rot0.
Qed.

End ListEmbedding.
