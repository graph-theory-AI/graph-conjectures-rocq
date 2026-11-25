(** * An obstruction to uniquely covered paths

    Let [r] be a relation on the vertices of a graph [G] and let the upset of a vertex [x] be the
    set of the vertices reachable from [x] in [r].  Suppose that the upsets are stable and that,
    for two vertices with a common neighbour, at least one is reachable from the other.  Then [G]
    is triangle-free and no path with at least three vertices is uniquely covered by the upsets. *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Obstruction.
Variables (G : sgraph) (r : rel G).
Hypothesis comparable : forall u v w : G, u -- v -> v -- w -> connect r u w || connect r w u.
Hypothesis stable_upset : forall x : G, stable [set y | connect r x y].

Lemma upset_triangle_free : triangle_free G.
Proof.
move=> x y z xy yz zx; wlog c : x z xy yz zx / connect r x z => [hw|].
  by case/orP: (comparable xy yz) => c; [apply: hw c | apply: hw c]; rewrite // sgP.
by have /stableP/(_ x z) := stable_upset x; rewrite !inE connect0 c sgP zx => /(_ isT isT).
Qed.

Lemma upset_not_uniquely_covered (p : seq G) :
  2 < size p -> uniq p -> sorted (--) p ->
  ~ forall v : G, v \in p -> exists x : G, [set y | connect r x y] :&: [set:: p] = [set v].
Proof.
case: p => [|a [|b [|c p]]] //= _ /andP[a_p _] /and3P[ab bc _] cov.
have neq_ac : a != c by apply: contraNneq a_p => ->; rewrite !inE eqxx orbT.
have not_le v w : v \in [:: a, b, c & p] -> w \in [:: a, b, c & p] -> connect r v w -> v = w.
  move=> /cov[x /setP eq_x] w_p vw; apply/esym/set1P; rewrite -eq_x !inE.
  by have := eq_x v; rewrite !inE eqxx => /andP[/connect_trans-> //].
case/orP: (comparable ab bc) => [/not_le | /not_le] eq_ac; case/eqP: neq_ac.
  by apply: eq_ac; rewrite !inE eqxx ?orbT.
by apply/esym/eq_ac; rewrite !inE eqxx ?orbT.
Qed.

End Obstruction.
