(** * Walks and arcs on a cycle

Arithmetic part of the disproof: the vertices of a cycle C of length n are the numbers smaller
than n, called positions. *)

From mathcomp Require Import boot zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Walks.
Variable n : nat.

(** The position [j] follows [i]. *)
Definition succ_pos (i j : nat) : bool := (j == i.+1) || ((i.+1 == n) && (j == 0)).

Lemma succ_posE i j : i < n -> j < n -> (i.+1 %% n == j) = succ_pos i j.
Proof.
move=> lt_i lt_j; rewrite /succ_pos; have [e|ne] := eqVneq i.+1 n.
  by rewrite e modnn; lia.
by rewrite modn_small; lia.
Qed.

(** [f] is a walk with [m] vertices on C, without immediate return. *)
Definition walk m (f : nat -> nat) : Prop :=
  [/\ forall i, f i < n,
      forall i, i.+1 < m -> succ_pos (f i) (f i.+1) || succ_pos (f i.+1) (f i)
    & forall i, i.+2 < m -> f i.+2 <> f i].

(** A walk without immediate return always goes in the same direction. *)
Lemma walk_monotone m f : walk m f -> 1 < m <= n ->
  (forall i, i < m -> f i = f 0 + i \/ f i + n = f 0 + i) \/
  (forall i, i < m -> f 0 = f i + i \/ f 0 + n = f i + i).
Proof.
move=> [lt_f step turn] /andP [m1 mn]; rewrite /succ_pos in step.
have {}lt_f i : f i < n /\ f i.+1 < n /\ f 0 < n by [].
case/orP: (step 0 m1) => s0; [left|right]; case=> [|i lt_i]; try lia.
- suff [] : succ_pos (f i) (f i.+1) /\ (f i.+1 = f 0 + i.+1 \/ f i.+1 + n = f 0 + i.+1) by [].
  rewrite /succ_pos; elim: i lt_i => [|i IH] lt_i; first lia.
  have := IH (ltnW lt_i); have := step _ lt_i; have := turn _ lt_i.
  have := lt_f i.+1; have := lt_f i; lia.
- suff [] : succ_pos (f i.+1) (f i) /\ (f 0 = f i.+1 + i.+1 \/ f 0 + n = f i.+1 + i.+1) by [].
  rewrite /succ_pos; elim: i lt_i => [|i IH] lt_i; first lia.
  have := IH (ltnW lt_i); have := step _ lt_i; have := turn _ lt_i.
  have := lt_f i.+1; have := lt_f i; lia.
Qed.

(** A closed walk without immediate return has length at least [n]. *)
Lemma closed_walk m f : walk m f -> 2 < m ->
  succ_pos (f 0) (f m.-1) || succ_pos (f m.-1) (f 0) -> n <= m.
Proof.
move=> w m2; rewrite leqNgt => cl; apply/negP => lt_m.
have m1n : 1 < m <= n by lia.
move: cl; rewrite /succ_pos.
by have [H|H] := walk_monotone w m1n; have := H m.-1; lia.
Qed.

End Walks.

Section Arcs.
Variable q : nat.
Abbreviation n := (3 * q).

(** The position [i] is on the arc [A_k] ([k < 3]) of C, which goes from [k * q] to [(k + 1) * q]
    (that is 0 if [k = 2]). *)
Definition inarc (k i : nat) : bool := (k * q <= i <= k * q + q) || ((k == 2) && (i == 0)).

(** The length of a walk that leaves [A_a] at its first step and enters [A_b] at its last step. *)
Lemma walk_between_arcs m a b f : walk n m f -> 1 < m <= n -> a < 3 -> b < 3 ->
  inarc a (f 0) -> ~~ inarc a (f 1) -> ~~ inarc b (f m.-2) -> inarc b (f m.-1) ->
  m.-1 = if a == b then 2 * q else q.
Proof.
move=> w m1 a3 b3; have [lt_f _ _] := w.
have := lt_f 0; have := lt_f 1; have := lt_f m.-1; have := lt_f m.-2.
have [mono|mono] := walk_monotone w m1;
have := mono 1; have := mono m.-1; have := mono m.-2; rewrite /inarc.
all: case: a a3 => [|[|[|//]]] _; case: b b3 => [|[|[|//]]] _.
all: rewrite ?mul0n ?mul1n /=.
all: lia.
Qed.

(** An interval of C with less than [q] edges misses some arc. *)
Lemma interval_misses_arc i0 m : i0 < n -> m < q ->
  exists2 k, k < 3 & forall j, j < n -> i0 <= j <= i0 + m \/ j + n <= i0 + m -> ~~ inarc k j.
Proof.
move=> lt_i0 lt_m; rewrite /inarc.
have [h0|h0] := posnP i0; first by exists 1 => // j; lia.
have [h1|h1] := leqP i0 q; first by exists 2 => // j; lia.
have [h2|h2] := leqP i0 (2 * q); first by exists 0 => // j; lia.
by exists 1 => // j; lia.
Qed.

End Arcs.
