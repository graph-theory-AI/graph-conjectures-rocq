(** * The conjecture fails for T = Δ(1,2,2)

T is the tournament [delta_1_2_2]: a directed triangle c -> A -> B -> c where A and B are
replaced by arcs a0 -> a1 and b0 -> b1.  Each T-free tournament R on the natural numbers has a
T-free locally finite perturbation.  For an arc x -> y, consider the vertices p of its gap
(x -> p -> y) and the third vertices z of its directed triangles (y -> z -> x).
- If some arc x -> y has an empty gap, reverse it.  In a copy of T that uses the new arc y -> x,
  no vertex t satisfies x -> t -> y.  Therefore x and y are twins in this copy (the arc y -> x
  corresponds to a0 -> a1 or b0 -> b1), and exchanging them gives a copy of T in R.
- If R is transitive, reverse the arc between 0 and 1.  Each directed triangle then contains 0
  and 1, whereas T has two directed triangles with only one common vertex.
- Otherwise R has a directed triangle x -> y -> z -> x, and no gap is empty.  As R is T-free, each
  arc is in at most two directed triangles.  Thus x and y have the same out-neighbours, up to
  finitely many, and the transposition of x and y transforms R into an isomorphic tournament,
  which is a locally finite perturbation of R.
These properties are not decidable, but the case distinction is made in a proof of [False].

The counterexample comes from Graph-Theory-LLM-Proofs (attacks_retry/2506.08810__03).  Its proof
was made constructive and formalized in graph-theory-rocq
(infinite-graph-theory/theories/applications/tournament_perturbation). *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require Import digraph.
From GC.infinite.AX_induced_saturated_infinite_tournament_perturbation Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation nat_tournament := main.nat_tournament.
Abbreviation has_subtournament := main.has_subtournament.
Abbreviation locally_finite_perturbation := main.locally_finite_perturbation.

(** ** Arcs of tournaments *)

Lemma arc_neq (R : rel nat) (x y : nat) : nat_tournament R -> R x y -> x != y.
Proof. by case=> irR _; apply: contraTneq => ->; rewrite irR. Qed.

Lemma arc_rev (R : rel nat) (x y : nat) : nat_tournament R -> x != y -> R y x = ~~ R x y.
Proof. by case=> _ totR; rewrite totR; case: (R x y); case: (R y x). Qed.

Lemma arc_asym (R : rel nat) (x y : nat) : nat_tournament R -> R x y -> R y x = false.
Proof. by move=> cR xy; rewrite (arc_rev cR (arc_neq cR xy)) xy. Qed.

(** If a tournament has the arcs x -> y -> z and not the arc x -> z, then it has the arc z -> x. *)
Lemma arc_triangle (R : rel nat) (x y z : nat) :
  nat_tournament R -> R x y -> R y z -> ~~ R x z -> R z x.
Proof.
move=> cR xy yz xz; rewrite (arc_rev cR) //.
by apply: contraTneq yz => <-; rewrite (arc_asym cR xy).
Qed.

(** A map from a tournament that preserves the arcs is a copy. *)
Lemma copy_of_arcs (T : diGraph) (R : rel nat) (f : T -> nat) :
  tournament T -> nat_tournament R -> (forall u v : T, u -- v -> R (f u) (f v)) ->
  has_subtournament T R.
Proof.
move=> [_ totT] cR fR; have arc u v : u != v -> f u != f v /\ (u -- v) = R (f u) (f v).
  rewrite totT; case uv: (u -- v) => /= vu.
    by rewrite (fR _ _ uv) (arc_neq cR (fR _ _ uv)).
  by rewrite eq_sym (arc_neq cR (fR _ _ vu)) (arc_asym cR (fR _ _ vu)).
exists f; split=> [u v /eqP fuv|u v /arc[]//].
by apply: contraTeq fuv => /arc[].
Qed.

(** Conversely, a copy preserves arcs and non-arcs. *)
Lemma copy_arcs (T : diGraph) (R : rel nat) :
  tournament T -> nat_tournament R -> has_subtournament T R ->
  exists f : T -> nat, injective f /\ forall u v : T, (u -- v) = R (f u) (f v).
Proof.
move=> [irT _] [irR _] [f [f_inj fR]]; exists f; split=> // u v.
by have [->|/fR] := eqVneq u v; first rewrite irT irR.
Qed.

(** ** Arc reversal *)

(** Reversal of the arc between [x] and [y]. *)
Definition flip (R : rel nat) (x y : nat) : rel nat :=
  fun u v => if (u == x) && (v == y) || (u == y) && (v == x) then R v u else R u v.

Lemma flip_perturbation (R : rel nat) (x y : nat) :
  nat_tournament R -> x != y -> locally_finite_perturbation R (flip R x y).
Proof.
move=> cR xy; split; first split.
- by move=> u; rewrite /flip if_same; case: cR.
- move=> u v; rewrite /flip orbC andbC [(u == x) && _]andbC.
  by case: ifP => _; case: cR => _ ->; rewrite // addbC.
- by exists x, y; rewrite /flip !eqxx (arc_rev cR xy); case: (R x y).
- move=> v; exists (maxn x y).+1 => u; rewrite gtn_max => /andP[xu yu].
  by rewrite /flip (gtn_eqF xu) (gtn_eqF yu) !andbF.
Qed.

(** ** The tournament T *)

Abbreviation T := delta_1_2_2.

Lemma tournament_T : tournament T.
Proof.
split; first by move=> [[a|a]|a]; exact: ltnn.
by move=> [[[[|//]?]|[[|[|//]]?]]|[[|[|//]]?]] [[[[|//]?]|[[|[|//]]?]]|[[|[|//]]?]].
Qed.

Abbreviation c := (inl (inl ord0) : T).
Abbreviation a0 := (inl (inr ord0) : T).
Abbreviation a1 := (inl (inr ord_max) : T).
Abbreviation b0 := (inr ord0 : T).
Abbreviation b1 := (inr ord_max : T).

Lemma T_not_transitive : ~ transitive (@edge_rel T).
Proof. by move/(_ a0 c b0 isT isT). Qed.

(** If no vertex [t] of T satisfies [u -- t -- w], where [w -- u], then [u] and [w] are twins. *)
Lemma T_twins (u w : T) :
  w -- u -> (forall t : T, u -- t -> ~~ (t -- w)) ->
  forall t : T, t != u -> t != w -> ((u -- t) = (w -- t)) * ((t -- u) = (t -- w)).
Proof.
case: u => [[u|u]|u]; case: w => [[w|w]|w] //= wu gap.
- by move: wu; rewrite (ord1 u) (ord1 w).
- by have := gap a0 isT.
- by have := gap b0 isT.
- case=> [[t|t]|t] // tu tw; move: u w t wu {gap} tu tw.
  by do 3![case=> [[|[|//]]?]].
- by have := gap c isT.
- case=> [[t|t]|t] // tu tw; move: u w t wu {gap} tu tw.
  by do 3![case=> [[|[|//]]?]].
Qed.

(** Five vertices with the arcs of T give a copy of T. *)
Lemma copy_T (R : rel nat) (z x0 x1 y0 y1 : nat) :
  nat_tournament R ->
  R z x0 -> R z x1 -> R x0 x1 -> R x0 y0 -> R x0 y1 -> R x1 y0 -> R x1 y1 ->
  R y0 y1 -> R y0 z -> R y1 z ->
  has_subtournament T R.
Proof.
move=> cR ? ? ? ? ? ? ? ? ? ?.
apply: (@copy_of_arcs T R (fun v : T => match v with
  | inl (inl _) => z
  | inl (inr i) => if i == ord0 then x0 else x1
  | inr i => if i == ord0 then y0 else y1
  end)) => //; first exact: tournament_T.
by move=> [[[[|//]?]|[[|[|//]]?]]|[[|[|//]]?]] [[[[|//]?]|[[|[|//]]?]]|[[|[|//]]?]].
Qed.

(** ** Reversal of an arc with an empty gap *)

Lemma flip_gap (R : rel nat) (x y : nat) :
  nat_tournament R -> ~ has_subtournament T R -> R x y -> (forall p, R x p -> ~~ R p y) ->
  ~ has_subtournament T (flip R x y).
Proof.
move=> cR freeR xy gap; have [cR' _ _] := flip_perturbation cR (arc_neq cR xy).
case/(copy_arcs tournament_T cR') => f [f_inj fR].
have copy g : (forall u v : T, u -- v -> R (g u) (g v)) -> False.
  by move/(copy_of_arcs tournament_T cR).
case: (pickP (fun u => f u == x)) => [u /eqP fu|x_f]; last first.
  by apply: (copy f) => u v; rewrite fR /flip !x_f andbF.
case: (pickP (fun w => f w == y)) => [w /eqP fw|y_f]; last first.
  by apply: (copy f) => v v'; rewrite fR /flip !y_f andbF.
subst x y; have irrT := proj1 tournament_T.
have uw : u != w by rewrite -(inj_eq f_inj) (arc_neq cR xy).
have wu : w -- u by rewrite fR /flip !eqxx orbT.
have uwF : u -- w = false by rewrite fR /flip !eqxx (arc_asym cR xy).
(* the other arcs of the copy are arcs of R *)
have fRT v t : v != u -> v != w -> ((v -- t) = R (f v) (f t)) * ((t -- v) = R (f t) (f v)).
  by move=> /negbTE vu /negbTE vw; rewrite !fR /flip !(inj_eq f_inj) vu vw !andbF.
have twins v : v != u -> v != w -> ((u -- v) = (w -- v)) * ((v -- u) = (v -- w)).
  apply: T_twins => // t ut; have tu : t != u by apply: contraTneq ut => ->; rewrite irrT.
  have [->|tw] := eqVneq t w; first by rewrite irrT.
  by rewrite fRT // gap // -(fRT t).
apply: (copy (f \o [fun v => v with u |-> w, w |-> u])) => v v' /=.
case: (eqVneq v u) => [->|vu]; case: (eqVneq v' u) => [->|v'u]; rewrite ?irrT //.
- by case: (eqVneq v' w) => [->|v'w]; rewrite ?uwF // twins // (fRT v').
- by case: (eqVneq v w) => [//|vw]; rewrite twins // (fRT v).
- case: (eqVneq v w) => [->|vw]; case: (eqVneq v' w) => [->|v'w]; rewrite ?irrT //.
  + by rewrite -twins // (fRT v').
  + by rewrite -twins // (fRT v).
  + by rewrite fRT.
Qed.

(** ** Transitive case *)

Lemma flip_transitive (R : rel nat) (x y : nat) :
  nat_tournament R -> transitive R -> x != y -> ~ has_subtournament T (flip R x y).
Proof.
move=> cR transR xy; have [cR' _ _] := flip_perturbation cR xy.
case/(copy_arcs tournament_T cR') => f [f_inj fR].
(* each directed triangle contains x and y *)
have triangle (u v w : T) : u -- v -> v -- w -> w -- u ->
    (x \in [:: f u; f v; f w]) && (y \in [:: f u; f v; f w]).
  rewrite !fR /flip !inE.
  do 3![case: ifP => [/orP[]/andP[/eqP-> /eqP->]|_]; rewrite ?eqxx ?orbT //].
  by move=> uv vw; rewrite (arc_asym cR (transR _ _ _ uv vw)).
have /andP[x0 y0] := triangle c a0 b0 isT isT isT.
have /andP[x1 y1] := triangle c a1 b1 isT isT isT.
(* the directed triangles c a0 b0 and c a1 b1 have only c in common *)
have common z : z \in [:: f c; f a0; f b0] -> z \in [:: f c; f a1; f b1] -> z = f c.
  by rewrite !inE => /or3P[]/eqP-> //; rewrite !(inj_eq f_inj).
by rewrite (common x) // (common y) ?eqxx in xy.
Qed.

(** ** Transposition of two vertices *)

(** Let p be in the gap of an arc x -> y of a T-free tournament.  For each orientation of the arc
    between p and z, there is at most one vertex z such that y -> z and not x -> z (therefore
    z -> x). *)
Lemma triangle_uniq (R : rel nat) (x y p z w : nat) :
  nat_tournament R -> ~ has_subtournament T R -> R x y -> R x p -> R p y ->
  R y z -> ~~ R x z -> R y w -> ~~ R x w -> R p z = R p w -> z = w.
Proof.
move=> cR freeR xy xp py yz xz yw xw pzw; apply/eqP; apply: contraT => zw; exfalso.
wlog {zw} zw : z w yz xz yw xw pzw / R z w.
  move=> IH; case zRw: (R z w); first exact: (IH z w).
  by apply: (IH w z) => //; rewrite (arc_rev cR zw) zRw.
have zx := arc_triangle cR xy yz xz; have wx := arc_triangle cR xy yw xw.
apply: freeR; case pz: (R p z).
  by apply: (copy_T (z := x) (x0 := p) (x1 := y) (y0 := z) (y1 := w)); rewrite -?pzw.
have zp : R z p by rewrite (arc_triangle cR py yz) ?pz.
have wp : R w p by rewrite (arc_triangle cR py yw) -?pzw ?pz.
exact: (copy_T (z := y) (x0 := z) (x1 := w) (y0 := x) (y1 := p)).
Qed.

(** For an arc x -> y with a nonempty gap, the out-neighbours of y are out-neighbours of x, except
    finitely many (under a double negation). *)
Lemma triangle_bounded (R : rel nat) (x y : nat) :
  nat_tournament R -> ~ has_subtournament T R -> R x y -> ~ (forall p, R x p -> ~~ R p y) ->
  ~ ~ exists N, forall z, N <= z -> R y z -> R x z.
Proof.
move=> cR freeR xy gap unb; apply: gap => p xp; apply/negP => py.
(* at most one exception z for each orientation *)
have bounded b : ~ ~ exists N, forall z, N <= z -> R y z -> R p z = b -> R x z.
  move=> unb_b; apply: (unb_b); exists 0 => z _ yz pz; apply: contraT => xz.
  exfalso; apply: unb_b; exists z.+1 => w lt_zw yw pw; apply: contraT => xw.
  by rewrite (triangle_uniq cR freeR xy xp py yz xz yw xw) ?ltnn // pz in lt_zw.
apply: (bounded true) => -[N NP]; apply: (bounded false) => -[M MP].
apply: unb; exists (maxn N M) => z; rewrite geq_max => /andP[/NP Nz /MP Mz] yz.
by case pz: (R p z); [exact: Nz | exact: Mz].
Qed.

(** The transposition of two vertices with the same out-neighbours, up to finitely many. *)
Lemma swap_perturbation (R : rel nat) (x y N : nat) :
  nat_tournament R -> R x y -> (forall u, N <= u -> R x u = R y u) ->
  let s : nat -> nat := [fun u => u with x |-> y, y |-> x] in
  locally_finite_perturbation R (fun u v => R (s u) (s v)).
Proof.
move=> cR xy big s; have [irR totR] := cR.
have sK : involutive s.
  move=> u; rewrite /s /=; case: (eqVneq u x) => [->|ux]; first by rewrite eqxx; case: eqVneq.
  by case: (eqVneq u y) => [->|uy]; rewrite ?eqxx // (negbTE ux) (negbTE uy).
split; first by split=> [u|u v] //; rewrite -totR (can_eq sK).
  exists x, y; rewrite (arc_neq cR xy) /s /= !eqxx [y == x]eq_sym.
  by rewrite (negbTE (arc_neq cR xy)) xy (arc_asym cR xy).
move=> v; exists (maxn N (maxn x y).+1) => u; rewrite geq_max gtn_max => /and3P[Nu xu yu].
rewrite /s /= (gtn_eqF xu) (gtn_eqF yu).
by case: (eqVneq v x) => [->|_]; last case: (eqVneq v y) => [->|_]; rewrite ?big.
Qed.

(** ** Conclusion *)

Theorem disproof : ~ main.AX_induced_saturated_infinite_tournament_perturbation.
Proof.
move=> /(_ T tournament_T T_not_transitive)[R [cR freeR HR]].
have gap x y : R x y -> ~ (forall p, R x p -> ~~ R p y).
  move=> xy nogap; have := HR _ (flip_perturbation cR (arc_neq cR xy)).
  exact: flip_gap.
have bounded x y xy := triangle_bounded cR freeR xy (gap x y xy).
have : ~ transitive R.
  move=> transR; have := HR _ (flip_perturbation cR (isT : 0 != 1)).
  exact: flip_transitive.
apply=> y x z xy yz; apply: contraT => /(arc_triangle cR xy yz) zx.
exfalso; apply: (bounded x y xy) => -[N1 yx].
apply: (bounded y z yz) => -[N2 zy]; apply: (bounded z x zx) => -[N3 xz].
(* x and y have the same out-neighbours, up to finitely many *)
have big u : maxn N1 (maxn N2 N3) <= u -> R x u = R y u.
  rewrite !geq_max => /and3P[/yx yxu /zy zyu /xz xzu].
  by apply/idP/idP => [/xzu/zyu|/yxu].
have lfR := swap_perturbation cR xy big; have [cR' _ _] := lfR.
have [f [_ fR]] := copy_arcs tournament_T cR' (HR _ lfR).
by apply: freeR; apply: (copy_of_arcs tournament_T cR) => u v; rewrite fR; apply.
Qed.
