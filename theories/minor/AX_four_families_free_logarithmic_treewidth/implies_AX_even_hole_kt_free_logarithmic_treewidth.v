(** * The four-families conjecture implies the (even hole, K_t)-free conjecture

Let t be given, and apply the first conjecture with s = max(t, 5).  A graph G with no even hole and
no clique on t vertices satisfies its four hypotheses:
- K_s is a clique on s >= t vertices;
- K_{s,s} contains an induced 4-cycle, which is an even hole;
- a subdivision of the wall W_{s×s} contains an induced theta: in the wall, the vertices (2,1) and
  (2,3) are joined by three paths of lengths 2, 4 and 10 whose unions are holes (of lengths 6, 12
  and 14); in a subdivision they become holes whose lengths add up to an even number, since each
  path is on two of them, so one of these holes is even;
- the edges of this even hole form an even hole of the line graph of the subdivision.
Holes are preserved by induced copies, so G contains none of the four families.

The implication is the edge e052 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (minor-theory/theories/conjectures/implications_X220.v). *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot zify_ssreflect.
From GC.GraphLib Require Import misc minor ramsey.
From GC.minor.AX_four_families_free_logarithmic_treewidth Require Import
  main(AX_four_families_free_logarithmic_treewidth).
From GC.minor.AX_even_hole_kt_free_logarithmic_treewidth Require Import
  main(AX_even_hole_kt_free_logarithmic_treewidth).

(** The definitions of the first conjecture. *)
Module A := GC.minor.AX_four_families_free_logarithmic_treewidth.main.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A test for holes that computes on concrete sequences: adjacent entries are the cyclically
    consecutive ones. *)
Definition holeb (G : sgraph) (c : seq G) : bool :=
  if c is x0 :: _ then
    [&& uniq c, 3 < size c & all (fun i => all (fun j =>
        (nth x0 c i -- nth x0 c j) == (i.+1 %% size c == j) || (j.+1 %% size c == i))
      (iota 0 (size c))) (iota 0 (size c))]
  else false.

Lemma holebP (G : sgraph) (c : seq G) : holeb c -> hole c.
Proof.
case: c => // x0 s /and3P[uc s4 /allP adj]; apply/(hole_nthP x0); split=> // i j ic jc.
have := adj i; rewrite mem_iota add0n ic => /(_ isT)/allP/(_ j).
by rewrite mem_iota add0n jc => /(_ isT)/eqP.
Qed.

(** ** Subdivisions of walls have even holes *)

Section Theta.
Variables (t : nat) (t5 : 4 < t).

Let vtx i j (i5 : i < 5) (j5 : j < 5) : wall t :=
  (Ordinal (leq_trans i5 t5), Ordinal (leq_trans j5 t5)).
Local Abbreviation v i j := (@vtx i j isT isT).

(** The theta of the wall: three paths between [v 2 1] and [v 2 3], of lengths 2, 4 and 10, and
    the three cycles that they form. *)
Definition theta_path1 : seq (wall t) := [:: v 2 1; v 2 2; v 2 3].
Definition theta_path2 : seq (wall t) := [:: v 2 1; v 1 1; v 1 2; v 1 3; v 2 3].
Definition theta_path3 : seq (wall t) :=
  [:: v 2 3; v 2 4; v 3 4; v 3 3; v 4 3; v 4 2; v 4 1; v 3 1; v 3 0; v 2 0; v 2 1].

Definition theta_cycle12 : seq (wall t) := [:: v 2 1; v 1 1; v 1 2; v 1 3; v 2 3; v 2 2].
Definition theta_cycle13 : seq (wall t) :=
  [:: v 2 1; v 2 2; v 2 3; v 2 4; v 3 4; v 3 3; v 4 3; v 4 2; v 4 1; v 3 1; v 3 0; v 2 0].
Definition theta_cycle23 : seq (wall t) :=
  [:: v 2 1; v 1 1; v 1 2; v 1 3; v 2 3; v 2 4; v 3 4; v 3 3; v 4 3; v 4 2; v 4 1; v 3 1; v 3 0;
      v 2 0].

Lemma theta_holes : [/\ hole theta_cycle12, hole theta_cycle13 & hole theta_cycle23].
Proof. by split; apply: holebP; vm_compute. Qed.

Lemma wall_subdivision_even_hole (W : sgraph) :
  is_subdivision_of W (wall t) -> exists2 d : seq W, hole d & ~~ odd (size d).
Proof.
case=> m sp; have [h12 h13 h23] := theta_holes.
pose w (p : seq (wall t)) := sumn [seq size (subdiv_path m q.1 q.2) | q <- zip p (behead p)].
have sym a b : a -- b -> w [:: b; a] = w [:: a; b].
  by move=> ab; rewrite /w /= (subdiv_pathC m ab) size_rev.
have H12 := subdiv_hole sp h12; set k12 := subdiv_walk _ _ _ in H12.
have H13 := subdiv_hole sp h13; set k13 := subdiv_walk _ _ _ in H13.
have H23 := subdiv_hole sp h23; set k23 := subdiv_walk _ _ _ in H23.
have E12 : size k12 = 6 + w theta_path2 + w theta_path1.
  have := sym (v 2 2) (v 2 3) isT; have := sym (v 2 1) (v 2 2) isT.
  by rewrite /k12 size_subdiv_walk /w /=; lia.
have E13 : size k13 = 12 + w theta_path1 + w theta_path3.
  by rewrite /k13 size_subdiv_walk /w /=; lia.
have E23 : size k23 = 14 + w theta_path2 + w theta_path3.
  by rewrite /k23 size_subdiv_walk /w /=; lia.
case o12 : (odd (size k12)); last by exists k12; [exact: H12 | exact: negbT o12].
case o13 : (odd (size k13)); last by exists k13; [exact: H13 | exact: negbT o13].
case o23 : (odd (size k23)); last by exists k23; [exact: H23 | exact: negbT o23].
move: o12 o13 o23; rewrite E12 E13 E23.
move: (w theta_path1) (w theta_path2) (w theta_path3) => a b c.
by rewrite !oddD /=; case: (odd a) (odd b) (odd c) => /= [] [] [].
Qed.

End Theta.

(** ** Complete bipartite graphs *)

Lemma complete_bipartite_hole s (s2 : 1 < s) :
  hole ([:: inl (Ordinal (ltnW s2)); inr (Ordinal (ltnW s2)); inl (Ordinal s2); inr (Ordinal s2)]
        : seq (KB s s)).
Proof. by apply: holebP; vm_compute. Qed.

(** ** The implication *)

(** The subdivisions of walls of the first conjecture are those of the library. *)
Lemma lib_wall_subdivision (W : sgraph) t :
  A.is_subdivision_of W (A.wall t) -> is_subdivision_of W (wall t).
Proof.
case=> m sp.
by exists (SubdivisionModel (H := wall t) (@A.subdiv_branch_inj _ _ m) (@A.subdiv_pathP _ _ m)
  (@A.subdiv_pathC _ _ m) (@A.subdiv_path_branch _ _ m) (@A.subdiv_path_disjoint _ _ m)).
Qed.

Theorem
  AX_four_families_free_logarithmic_treewidth_implies_AX_even_hole_kt_free_logarithmic_treewidth :
  AX_four_families_free_logarithmic_treewidth -> AX_even_hole_kt_free_logarithmic_treewidth.
Proof.
move=> four t; have [c Hc] := four (maxn t 5); exists c => G eh om.
have noeven (H : sgraph) :
    (exists2 d : seq H, hole d & ~~ odd (size d)) -> ~ has_induced_copy G H.
  by case=> d hd ev [i]; apply: (eh (map i d)); [apply: hole_isubgraph | rewrite size_map].
have t5 : 4 < maxn t 5 by rewrite leq_max ltnSn orbT.
apply: Hc.
- by move/has_induced_copy_Kn; rewrite leqNgt (leq_trans om) ?leq_maxl.
- by apply: noeven; eexists; first exact: complete_bipartite_hole (ltn_trans (isT : 1 < 4) t5).
- by move=> W /lib_wall_subdivision hW; apply/noeven/(wall_subdivision_even_hole t5 hW).
move=> W /lib_wall_subdivision hW; apply: noeven.
have [d hd ev] := wall_subdivision_even_hole t5 hW; have [d' hd' sd] := hole_line_graph hd.
by exists d'; rewrite ?sd.
Qed.

Check
  (AX_four_families_free_logarithmic_treewidth_implies_AX_even_hole_kt_free_logarithmic_treewidth :
GC.minor.AX_four_families_free_logarithmic_treewidth.main.AX_four_families_free_logarithmic_treewidth
  ->
GC.minor.AX_even_hole_kt_free_logarithmic_treewidth.main.AX_even_hole_kt_free_logarithmic_treewidth).
Print Assumptions
  AX_four_families_free_logarithmic_treewidth_implies_AX_even_hole_kt_free_logarithmic_treewidth.
