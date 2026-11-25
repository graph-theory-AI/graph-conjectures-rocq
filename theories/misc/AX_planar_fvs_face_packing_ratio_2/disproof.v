(** * A planar graph with feedback vertex number 5 and face packing number 2

The counterexample has 12 vertices: a 4-cycle and two cliques on 4 vertices, each attached by two
edges to opposite vertices of the 4-cycle.  Its feedback vertex number is 5 (one vertex of the
4-cycle and two vertices of each clique).  The 4-cycle is not a face of any embedding in the
plane, so every face meets a clique.  Two disjoint cycles cannot meet the same clique, so face
packings have at most two cycles.

The proof comes from Graph-Theory-LLM-Proofs (attacks_arxiv_astra/1912.01570__00), where the
Jordan curve theorem shows that the 4-cycle is not a face.  It was formalized in graph-theory-rocq
(graph-theory-misc/theories/applications/planar_fvs_face_packing), and is simplified here. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot fingroup perm.
From GC.GraphLib Require Import misc topological.
From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require Import graph facial.
From GC.misc.AX_planar_fvs_face_packing_ratio_2 Require main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation cycle_packing := main.cycle_packing.

(** ** At most one cycle of a packing meets a given clique *)

Definition clique_of (j : bool) : seq G12 :=
  if j then [:: p0; q0; r0; s0] else [:: p1; q1; r1; s1].

(** A cycle that meets a clique contains its two attachment vertices or three of its vertices.
    So two such cycles meet. *)
Lemma cycle_clique (s t : seq G12) j :
  seq_cycle (--) s -> seq_cycle (--) t ->
  has (mem s) (clique_of j) -> has (mem t) (clique_of j) -> has (mem t) s.
Proof.
move=> cs ct ms mt.
have trace u : seq_cycle (--) u -> has (mem u) (clique_of j) ->
    let x i := nth a (clique_of j) i \in u in
    [|| x 0 && x 1, x 0 && x 2 && x 3 | x 1 && x 2 && x 3].
  move=> cu; have deg v : (v \in u) ==> (1 < count (fun w => w \in u) (nb v)).
    by apply/implyP; exact: cycle_nb.
  case: j {ms mt} => /=.
    by move: (deg p0) (deg q0) (deg r0) (deg s0) => /=; do 6?case: (_ \in u).
  by move: (deg p1) (deg q1) (deg r1) (deg s1) => /=; do 6?case: (_ \in u).
apply/hasP; suff : has (mem t) [seq v <- clique_of j | v \in s].
  by case/hasP => v; rewrite mem_filter => /andP[vs _] vt; exists v.
move: (trace s cs ms) (trace t ct mt) => /=.
by case: j {ms mt trace} => /=; do 4!case: (_ \in s) => //=; do 4!case: (_ \in t) => //=.
Qed.

Lemma part_clique_of (v : G12) : part v != 0 -> v \in clique_of (part v == 1).
Proof.
apply/implyP; move: v.
exact: (all_vertices (P := fun v => (part v != 0) ==> (v \in clique_of (part v == 1)))).
Qed.

(** Every face meets a clique, so there are at most two disjoint faces. *)
Lemma face_packing_le2 (E : embedding G12) (cs : seq (seq G12)) :
  planar_embedding E -> cycle_packing cs ->
  (forall s, s \in cs -> exists x, face_walk E x = s) -> size cs <= 2.
Proof.
move=> pl [cyc cnt] faces; pose meets j (s : seq G12) := has (mem s) (clique_of j).
have le1 j : count (meets j) cs <= 1.
  rewrite -size_filter; case F: (filter _ _) => [|s [|t l]] //; exfalso.
  have st u : u \in [:: s; t] -> meets j u && (u \in cs).
    by move=> ust; rewrite -mem_filter F -[s :: _]/([:: s; t] ++ l) mem_cat ust.
  have /andP[ms s_cs] := st s (mem_head _ _).
  have /andP[mt t_cs] := st t (mem_last s [:: t]).
  have /hasP[v vs vt] := cycle_clique (cyc s s_cs) (cyc t t_cs) ms mt.
  have := leq_trans (leq_count_subseq _ (filter_subseq (meets j) cs)) (cnt v).
  by rewrite F /= vs [v \in t]vt.
have <- : count (predU (meets true) (meets false)) cs = size cs.
  apply/eqP; rewrite -all_count; apply/allP => _ /faces[x <-] /=.
  have [v vx pv] := face_leaves_cycle pl x.
  have : meets (part v == 1) (face_walk E x) by apply/hasP; exists v => //; exact: part_clique_of.
  by case: (part v == 1) => ->; rewrite ?orbT.
apply: leq_trans (leq_add (le1 true) (le1 false)).
by rewrite -count_predUI leq_addr.
Qed.

(** ** An embedding in the plane with two disjoint triangular faces *)

(** A function that is constant on the orbits of [s] gives a lower bound on their number. *)
Lemma card_porbits_ge (T : finType) (S : eqType) (s : {perm T}) (h : T -> S) (xs : seq T) :
  (forall x, h (s x) = h x) -> uniq (map h xs) -> size xs <= #|porbits s|.
Proof.
move=> hs; pose g (O : {set T}) := omap h [pick x in O].
have gE x : g (porbit s x) = Some (h x).
  rewrite /g; case: pickP => [y|/(_ x)]; last by rewrite porbit_id.
  by case/porbitP => i -> /=; rewrite permX; elim: i => //= i <-; rewrite hs.
rewrite -(map_inj_uniq (@Some_inj _)) -map_comp -(eq_map gE) map_comp => /map_uniq Uxs.
rewrite -(size_map (porbit s)) cardE; apply: uniq_leq_size => // _ /mapP[x _ ->].
by rewrite mem_enum imset_f.
Qed.

(** This embedding has 10 faces. *)
Definition E12 : embedding G12 := list_embedding nbP nbU.

Definition start (u v : G12) (uv : u -- v) : dart G12 := exist _ (u, v) uv.

(** A dart of each face. *)
Definition starts : seq (dart G12) :=
  [:: @start a b isT; @start a d isT; @start a p1 isT; @start b c isT;
      @start p0 q0 isT; @start p0 r0 isT; @start q0 s0 isT;
      @start p1 q1 isT; @start p1 r1 isT; @start q1 s1 isT].

(** The index in [starts] of the face of a dart. *)
Definition face_index (e : G12 * G12) : nat :=
  find (fun x => e \in traject (@list_face G12 nb) (val x) 6) starts.

Lemma E12_faces : 10 <= face_count (rotation E12).
Proof.
apply: (card_porbits_ge (h := fun x => face_index (val x)) (xs := starts)); last by vm_compute.
move=> x; rewrite -[(_ * _)%g]/(face_perm E12) list_face_perm.
have xE := svalP x; rewrite /= in xE.
have := all_edges (P := fun e => face_index (@list_face G12 nb e) == face_index e).
rewrite [in RHS](surjective_pairing (val x)) [in LHS](surjective_pairing (val x)).
by move=> H; apply/eqP; apply: H xE; vm_compute.
Qed.

Lemma E12_planar : planar_embedding E12.
Proof.
rewrite /planar_embedding /embedding_genus card_edges card_ord.
by rewrite (eqP (_ : 2 + 20 - 12 - _ == 0)) // subn_eq0 E12_faces.
Qed.

Definition triangles : seq (seq G12) := [:: [:: p0; r0; q0]; [:: p1; r1; q1]].

Lemma triangles_packing : cycle_packing triangles.
Proof.
split=> [s|v].
  by apply/allP: s; vm_compute.
by apply: (all_vertices (P := fun v => count (fun s => v \in s) triangles <= 1)); vm_compute.
Qed.

Lemma triangles_faces s : s \in triangles -> exists x, face_walk E12 x = s.
Proof.
by rewrite !inE => /orP[] /eqP->; [exists (@start p0 q0 isT)|exists (@start p1 q1 isT)];
   rewrite (list_face_walk nbP nbU (n := 3)); vm_compute.
Qed.

(** ** The counterexample *)

(** The embeddings of GraphLib and those of the statement are the same. *)
Definition of_main (E : main.embedding G12) : embedding G12 :=
  Emb (main.rotation_vertex E : forall x, porbit (main.rotation E) x = darts_at (sval x).1).

Lemma edge_perm_main : main.edge_perm G12 = edge_perm G12.
Proof. by apply/permP => x; rewrite !permE; apply: val_inj. Qed.

Lemma planar_embedding_main E : main.planar_embedding E <-> planar_embedding (of_main E).
Proof.
by rewrite /main.planar_embedding /main.embedding_genus /main.face_count edge_perm_main.
Qed.

Lemma face_walk_main E x : main.face_walk E x = face_walk (of_main E) x.
Proof. by rewrite /main.face_walk /main.face_perm edge_perm_main. Qed.

Definition E12_main : main.embedding G12 := main.Emb (list_rotation_vertex nbP nbU).

Lemma planar_E12_main : main.planar_embedding E12_main.
Proof. exact/planar_embedding_main/E12_planar. Qed.

Lemma face_packing_number_G12 : main.face_packing_number G12 2.
Proof.
split=> [|E cs /planar_embedding_main pl [cp faces]].
  exists E12_main; split; first exact: planar_E12_main.
  exists triangles; split=> //; split=> [|s /triangles_faces[x <-]].
    exact: triangles_packing.
  by exists x; exact: face_walk_main.
apply: face_packing_le2 pl cp _ => s /faces[x <-].
by exists x; rewrite face_walk_main.
Qed.

Theorem disproof : ~ main.AX_planar_fvs_face_packing_ratio_2.
Proof.
have planar : main.planar_graph G12 by exists E12_main; exact: planar_E12_main.
by move=> /(_ _ _ _ connected_G12 planar feedback_number_G12 face_packing_number_G12).
Qed.
