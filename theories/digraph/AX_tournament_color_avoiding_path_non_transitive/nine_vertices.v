(** * A tournament on 9 vertices with 6 colours and no long color-avoiding path

We prove f_{6,5}(9) = 8, and give a non-transitive 6-edge-coloured tournament on 9 vertices
whose longest color-avoiding paths have 7 vertices.

Lower bound on f_{6,5}(9).  Let v0, ..., v8 be the vertices of the transitive tournament, in
order.  Some colour c occurs at most once on the 11 arcs v_i v_{i+1} (0 <= i <= 7), v1 v3,
v3 v5 and v5 v7.  Consider the five paths on 8 vertices that omit v0, v2, v4, v6 and v8
respectively.  They use only these 11 arcs, and none of the arcs is used by all of them, so
one of the paths avoids c.

Upper bound on f_{6,5}(9).  Each arc v_i v_j has colour i modulo 6, hence the unique path on 9
vertices uses all colours.

The non-transitive tournament.  Three vertices l1, l2, l3, then a directed triangle x0, x1, x2,
then three vertices r1, r2, r3, with all other arcs from left to right.  The colours are
- 0 for l1 l2 and r2 r3,
- 1 for l1 l3, l2 l3 and l2 x_i,
- 2 for r1 r2, r1 r3 and x_i r2,
- 3+i for l3 x_(i+1), x_i x_(i+1) and x_i r1 (indices modulo 3),
the other ones being irrelevant.  A path on 8 vertices omits only one vertex, and one sees that it
uses all colours; l1, l2, l3, x0, x1, x2, r1 is a path that avoids colour 2.

Both upper bounds on the lengths of color-avoiding paths are checked by enumeration of the paths.

The proof comes from Graph-Theory-LLM-Proofs (attacks/2512.10438__00), with a simpler argument
for the lower bound.  It was formalized in graph-theory-rocq
(digraph-theory/theories/applications/color_avoiding_tournament). *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import digraph.
From GC.digraph.AX_tournament_color_avoiding_path_non_transitive Require main.
From mathcomp Require Import boot zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation color_avoiding := main.color_avoiding.
Abbreviation avoids_bound := main.avoids_bound.

(** The vertex [i] (modulo 9). *)
Abbreviation v i := (inZp i : 'I_9).

Abbreviation TT9 := (transitive_tournament 9).

(** ** Bounding the color-avoiding paths by enumeration *)

(** The elements of ['I_m.+1], as a list that can be computed. *)
Definition ords (m : nat) : seq 'I_m.+1 := map inZp (iota 0 m.+1).

Lemma mem_ords m (i : 'I_m.+1) : i \in ords m.
Proof. by apply/mapP; exists (val i); rewrite ?valZpK ?mem_iota ?ltn_ord. Qed.

Section Bound.
Variable e : rel 'I_9.

(** No path for [e] with [k] edges starts at [x] and avoids the vertices in [vis]. *)
Fixpoint no_path (k : nat) (vis : seq 'I_9) (x : 'I_9) : bool :=
  if k is k'.+1 then
    all (no_path k' (x :: vis)) [seq y <- ords 8 | e x y && (y \notin x :: vis)]
  else false.

Lemma no_pathP k vis x s :
  no_path k vis x -> path e x s -> uniq (catrev (x :: s) vis) -> size s < k.
Proof.
elim: k vis x s => [//|k IH] vis x [//|y s] /allP no /andP[xy ps] us.
apply: IH ps (us); apply: no; rewrite mem_filter xy mem_ords andbT /=.
by move: us; rewrite /= catrevE cat_uniq => /and3P[_ _ /andP[]].
Qed.

End Bound.

Lemma avoids_boundP (e : rel 'I_9) (chi : 'I_9 -> 'I_9 -> 'I_6) n :
  all (fun c => all (no_path (fun x y => e x y && (chi x y != c)) n [::]) (ords 8)) (ords 5) ->
  @avoids_bound (DiGraph e) 6 chi n.
Proof.
move=> /allP no x s /andP[_ us] /existsP[c avc].
apply: (no_pathP (allP (no c (mem_ords c)) x (mem_ords x)) avc).
by rewrite catrevE cats0 rev_uniq.
Qed.

(** ** The minimum over the transitive tournaments *)

(** Some value is taken at most once. *)
Lemma rare_value (A : Type) (C : finType) (f : A -> C) (s : seq A) :
  size s < 2 * #|C| -> exists c, count (fun a => f a == c) s <= 1.
Proof.
move=> small; apply/existsP; apply: contraLR small => /existsPn many.
rewrite -leqNgt -sum1_size (partition_big f xpredT) //= mulnC -sum_nat_const.
by apply: leq_sum => c _; rewrite sum1_count ltnNge many.
Qed.

Lemma transitive_path (chi : TT9 -> TT9 -> 'I_6) :
  exists (x : TT9) (s : seq TT9), [/\ dipath x s, color_avoiding chi x s & size (x :: s) = 8].
Proof.
pose arcs := [seq (i, i.+1) | i <- iota 0 8] ++ [:: (1, 3); (3, 5); (5, 7)].
pose paths := [seq rem k (iota 0 9) | k <- [:: 0; 2; 4; 6; 8]].
have omit : all (fun a => has (fun p => [&& @dipath TT9 (v (head 0 p)) (map inZp (behead p)),
    size p == 8 & path (fun i j => [&& v i < v j, (i, j) \in arcs & (i, j) != a])
      (head 0 p) (behead p)]) paths) arcs by vm_compute.
have [c] : exists c, count (fun a => chi (v a.1) (v a.2) == c) arcs <= 1.
  by apply: rare_value; rewrite card_ord.
rewrite -size_filter => rare.
have [a a_in aP] : exists2 a, a \in arcs &
    forall b, b \in arcs -> b != a -> chi (v b.1) (v b.2) != c.
  have := mem_filter (fun a => chi (v a.1) (v a.2) == c) _ arcs.
  case: filter rare => [|a [|//]] _ rP.
    by exists (0, 1) => // b b_in _; have := rP b; rewrite b_in andbT => /esym/negbT.
  have := rP a; rewrite mem_head => /esym/andP[_ a_in].
  by exists a => // b b_in; have := rP b; rewrite inE b_in andbT => <-.
have /hasP[p _ /and3P[dp /eqP sp arcs_p]] := allP omit a a_in.
exists (v (head 0 p)), (map inZp (behead p)); split=> //.
  apply/existsP; exists c; rewrite /main.avoiding path_map; apply: sub_path arcs_p => i j.
  by case/and3P=> ij /aP cij /cij ?; apply/andP.
by rewrite /= size_map size_behead sp.
Qed.

(** The colour of the arc from [v i] to [v j] is [i] modulo 6. *)
Definition transitive_color (x y : TT9) : 'I_6 := inZp x.

Lemma transitive_minimum : main.transitive_minimum_is 6 9 8.
Proof.
split=> [chi|].
  by have [x [s [ps av ss]]] := transitive_path chi; exists x, s; rewrite ss.
exists transitive_color; split; last exact: transitive_path.
by apply: avoids_boundP; vm_compute.
Qed.

(** ** The non-transitive tournament *)

(** The vertices 0, ..., 8 are l1, l2, l3, x0, x1, x2, r1, r2, r3. *)
Definition nine : diGraph :=
  DiGraph [rel x y : 'I_9 | (x < y) (+) (((x, y) == (v 3, v 5)) || ((x, y) == (v 5, v 3)))].

Lemma nine_tournament : tournament nine.
Proof.
have /allP nineP : all (fun x : nine => ~~ (x -- x) &&
  all (fun y => (x != y) == (x -- y) (+) (y -- x)) (ords 8)) (ords 8) by vm_compute.
split=> [x|x y]; have /andP[/negbTE loop /allP arcs] := nineP x (mem_ords x) => //.
exact: eqP (arcs y (mem_ords y)).
Qed.

Lemma nine_not_transitive : ~ transitive (@edge_rel nine).
Proof. by move=> /(_ (v 4) (v 3) (v 5) isT isT). Qed.

(** The rows and columns are indexed by the vertices (the row of r3 is missing).  The entries
    of the couples that are not arcs, and of the arcs l_i r_j, l1 x_i and x_i r3, do not
    matter. *)
Definition color_table : seq (seq nat) := [::
  [:: 0; 0; 1; 0; 0; 0; 0; 0; 0];
  [:: 0; 0; 1; 1; 1; 1; 0; 0; 0];
  [:: 0; 0; 0; 5; 3; 4; 0; 0; 0];
  [:: 0; 0; 0; 0; 3; 0; 3; 2; 0];
  [:: 0; 0; 0; 0; 0; 4; 4; 2; 0];
  [:: 0; 0; 0; 5; 0; 0; 5; 2; 0];
  [:: 0; 0; 0; 0; 0; 0; 0; 2; 2];
  [:: 0; 0; 0; 0; 0; 0; 0; 0; 0]].

Definition nine_color (x y : nine) : 'I_6 := inZp (nth 0 (nth [::] color_table x) y).

Lemma nine_longest : main.longest_avoiding_vertices nine_color 7.
Proof.
split; first by apply: avoids_boundP; vm_compute.
exists (v 0), (map inZp (iota 1 6)); split=> //.
by apply/existsP; exists (inZp 2); vm_compute.
Qed.

(** ** Main result *)

Theorem non_transitive_nine : main.AX_tournament_color_avoiding_path_non_transitive.
Proof.
exists 6, 9, nine, nine_color, 7, 8; split; split=> //.
- exact: nine_tournament.
- exact: card_ord.
- exact: nine_not_transitive.
- exact: nine_longest.
- exact: transitive_minimum.
Qed.
