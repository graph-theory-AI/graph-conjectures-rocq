(** * Nowhere-zero 4-flows from two even subgraphs

A balanced orientation of a set of edges [C] gives an integer flow with values [1] and [-1] on
[C] and [0] elsewhere ([osgn_conservative]).  Every even subgraph has a balanced orientation
([even_balanced_orientation]).  If two even subgraphs [C1] and [C2] cover exactly the edges
outside [A], the sum of the flow of [C1] and twice the flow of [C2] is a nowhere-zero 4-flow of
[G \ A] ([two_even_flow]). *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot ssralg ssrnum ssrint.
From GC.GraphLib Require Import misc cycle even_subgraph flow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Flows *)

Section Flows.
Variable G : mgraph.
Implicit Types (A C : {set edge G}) (o : edge G -> bool).
Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** Two even subgraphs that cover exactly the edges outside [A] give a nowhere-zero 4-flow of the
    graph [G] without the edges of [A]. *)
Lemma two_even_flow A C1 C2 : even_subgraph C1 -> even_subgraph C2 ->
  (forall e, (e \in C1) || (e \in C2) = (e \notin A)) -> nowhere_zero_flow (remove_edges A) 4.
Proof.
move=> /even_balanced_orientation[o1 b1] /even_balanced_orientation[o2 b2] cov.
pose phi e := osgn C1 o1 e + 2%:R * osgn C2 o2 e.
have phiA e : e \in A -> phi e = 0.
  move=> eA; have := cov e; rewrite eA /phi /osgn => /norP[/negbTE -> /negbTE ->].
  by rewrite mulr0 addr0.
have sub (P : pred (edge G)) :
    \sum_(e : edge (remove_edges A) | P (val e)) phi (val e) = \sum_(e | P e) phi e.
  rewrite -(big_sub_cond [pred e | e \notin A]) [RHS](bigID [pred e | e \notin A]) /=.
  rewrite [X in _ + X]big1 ?addr0 => [e /andP[_ /negbNE /phiA //]|].
  by apply: eq_bigl => e; rewrite andbC.
exists (fun e : edge (remove_edges A) => phi (val e)); split.
  move=> v; rewrite (sub (fun e => source e == v)) (sub (fun e => target e == v)).
  by rewrite !big_split /= -!mulr_sumr (osgn_conservative b1 v) (osgn_conservative b2 v).
case=> e /= eA; have := cov e; rewrite (negbTE eA) /phi /osgn.
by case: (e \in C1); case: (e \in C2); case: (o1 e); case: (o2 e).
Qed.

End Flows.
