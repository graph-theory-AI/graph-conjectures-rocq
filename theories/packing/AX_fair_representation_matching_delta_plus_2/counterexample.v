(** * Five copies of K_4 and six classes of five edges

Let H consist of five disjoint copies of K_4, so that Delta(H) + 2 = 5.  The edges of a copy are
partitioned into three perfect matchings, and the 30 edges are partitioned into six classes of size
5, numbered from 0 to 5, as follows (each pair gives the classes of the edges of a perfect
matching).

  copy 0: 11, 00, 00    copy 1: 11, 01, 45    copy 2: 22, 33, 33    copy 3: 22, 44, 55
  copy 4: 44, 23, 55

No matching M meets the six classes.  Indeed, M is included in a union of perfect matchings of the
copies [same_matching].  As classes 0 and 1 appear only in copies 0 and 1, and copy 0 does not give
both, copy 1 gives 0 or 1.  Then classes 4 and 5 come from copies 3 and 4, one from each, but
copy 2 does not give both 2 and 3.  In Rocq, the 3^5 choices of perfect matchings are checked
[class_missed].

The graph comes from a disproof in graph-theory-rocq (branch fair-matching-edge-part), with another
partition. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From GC.packing.AX_fair_representation_matching_delta_plus_2 Require Import main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The edges are numbered from 0 to 29: edge k is in copy k/6, and in the perfect matching
    (k mod 6)/2 of this copy. *)
Definition copy (k : nat) : nat := k %/ 6.
Definition pm (k : nat) : nat := k %% 6 %/ 2.

(** The ends of the edges: the vertices of copy i are 4i, ..., 4i + 3. *)
Definition ends_table : seq (nat * nat) := Eval compute in
  [seq (4 * i + e.1, 4 * i + e.2) |
     i <- iota 0 5, e <- [:: (0, 1); (2, 3); (0, 2); (1, 3); (0, 3); (1, 2)]].

Definition ends (k : nat) : nat * nat := nth (0, 0) ends_table k.

Definition class (k : nat) : nat :=
  nth 0 [:: 1; 1; 0; 0; 0; 0;   1; 1; 0; 1; 4; 5;   2; 2; 3; 3; 3; 3;   2; 2; 4; 4; 5; 5;
            4; 4; 2; 3; 5; 5] k.

(** Two vertices are adjacent if they are in the same copy. *)
Definition adj (x y : 'I_20) : bool := (x != y) && (x %/ 4 == y %/ 4).

Lemma adj_sym : symmetric adj.
Proof. by move=> x y; rewrite /adj eq_sym [_ %/ _ == _]eq_sym. Qed.

Lemma adj_irrefl : irreflexive adj.
Proof. by move=> x; rewrite /adj eqxx. Qed.

Definition H : sgraph := SGraph adj_sym adj_irrefl.

Definition edge (k : 'I_30) : {set H} :=
  [set v : 'I_20 | val v \in [:: (ends k).1; (ends k).2]].

Definition E (i : 'I_6) : {set {set H}} := [set edge k | k : 'I_30 & class k == i].

Lemma card_ord_pred n (P : pred nat) : #|[set k : 'I_n | P k]| = count P (iota 0 n).
Proof. by rewrite cardsE cardE size_filter -val_enum_ord count_map enumT. Qed.

Lemma ord_all m (k : 'I_m) (P : pred nat) : all P (iota 0 m) -> P k.
Proof. by move=> /allP h; apply: h; rewrite mem_iota ltn_ord. Qed.

Lemma ord_all2 m n (k : 'I_m) (l : 'I_n) (P : nat -> pred nat) :
  all (fun k => all (P k) (iota 0 n)) (iota 0 m) -> P k l.
Proof. by move=> /(ord_all k)/(ord_all l). Qed.

(** ** The graph and the partition *)

Lemma edge_setU (k : 'I_30) (x y : H) : ends k = (val x, val y) -> edge k = [set x; y].
Proof. by move=> e; apply/setP => v; rewrite !inE e /= !val_eqE. Qed.

Lemma edgeE (k : 'I_30) : exists x y : H, x -- y /\ edge k = [set x; y].
Proof.
have /and4P[e1 e2 ne eq4] := ord_all k (P := fun k => [&& (ends k).1 < 20, (ends k).2 < 20,
  (ends k).1 != (ends k).2 & (ends k).1 %/ 4 == (ends k).2 %/ 4]) isT.
exists (Ordinal e1), (Ordinal e2); split; last by apply: edge_setU; case: ends e1 e2 ne eq4.
exact/andP.
Qed.

Lemma check_adj : all (fun x => all (fun y => (x != y) && (x %/ 4 == y %/ 4) ==>
  has (fun k => (ends k == (x, y)) || (ends k == (y, x))) (iota 0 30)) (iota 0 20)) (iota 0 20).
Proof. by vm_compute. Qed.

Lemma edgeP (e : {set H}) : reflect (exists k, e = edge k) (e \in E(H)).
Proof.
apply: (iffP idP) => [/edgesP[x [y [-> xy]]]|[k ->]]; last first.
  by have [x [y [xy ->]]] := edgeE k; rewrite in_edges.
have /implyP/(_ xy)/hasP[k] := ord_all2 x y check_adj.
rewrite mem_iota => k30 /orP[]/eqP exy; exists (Ordinal k30).
  by apply/esym/edge_setU.
by rewrite setUC; apply/esym/edge_setU.
Qed.

Lemma mem_edge (v : 'I_20) (k : 'I_30) :
  (v \in edge k) = (val v \in [:: (ends k).1; (ends k).2]).
Proof. exact: in_set. Qed.

Lemma check_inj : all (fun k => all (fun l =>
    all (fun v => (v \in [:: (ends k).1; (ends k).2]) == (v \in [:: (ends l).1; (ends l).2]))
      (iota 0 20) ==> (k == l)) (iota 0 30)) (iota 0 30).
Proof. by vm_compute. Qed.

Lemma edge_inj : injective edge.
Proof.
move=> k l kl; apply/val_inj/eqP; have /implyP := ord_all2 k l check_inj.
apply; apply/allP => v; rewrite mem_iota => v20; apply/eqP.
by have := congr1 (fun e : {set 'I_20} => Ordinal v20 \in e) kl; rewrite !mem_edge.
Qed.

Lemma check_meet : all (fun k => all (fun l => (copy k == copy l) && (pm k != pm l) ==>
  has (fun v => (v \in [:: (ends k).1; (ends k).2]) && (v \in [:: (ends l).1; (ends l).2]))
    (iota 0 20)) (iota 0 30)) (iota 0 30).
Proof. by vm_compute. Qed.

(** Two edges in distinct perfect matchings of a copy share a vertex. *)
Lemma edge_meet (k l : 'I_30) : copy k = copy l -> pm k != pm l ->
  exists x : H, x \in edge k /\ x \in edge l.
Proof.
move=> kl ne; have := ord_all2 k l check_meet.
rewrite kl eqxx ne => /hasP[v]; rewrite mem_iota => v20 /andP[vk vl].
by exists (Ordinal v20 : 'I_20); rewrite !mem_edge.
Qed.

(** ** A matching misses a class *)

Lemma H_partition : edge_partition E.
Proof.
split=> [e|i j ij].
  apply/edgeP/existsP => [[k ->]|[i /imsetP[k _ ->]]]; last by exists k.
  have k6 : class k < 6 by apply: (ord_all k (P := fun k => class k < 6)).
  by exists (Ordinal k6); apply: imset_f; rewrite inE.
rewrite -setI_eq0; apply/eqP/setP => e; rewrite !inE.
apply/negbTE/andP => -[/imsetP[k + ->] /imsetP[l + /edge_inj kl]].
by rewrite !inE -kl => /eqP ki /eqP kj; rewrite -val_eqE /= -ki -kj eqxx in ij.
Qed.

Lemma card_E i : #|E i| = 5.
Proof.
rewrite (card_imset _ edge_inj) (card_ord_pred _ (fun k => class k == i)); apply/eqP.
by apply: (ord_all i (P := fun i => count (fun k => class k == i) (iota 0 30) == 5)).
Qed.

Lemma Delta_H : Delta H <= 3.
Proof.
apply/bigmax_leqP => v _.
have -> : #|N(v)| = #|[set w : 'I_20 | (val v != w) && (v %/ 4 == w %/ 4)]|.
  by apply: eq_card => w; rewrite !inE.
rewrite (card_ord_pred _ (fun w => (val v != w) && (v %/ 4 == w %/ 4))).
exact: (ord_all v (P := fun v => count (fun w => (v != w) && (v %/ 4 == w %/ 4)) (iota 0 20) <= 3)).
Qed.

(** The lists of [k] numbers smaller than [n]. *)
Fixpoint words (n k : nat) : seq (seq nat) :=
  if k is k'.+1 then [seq x :: s | x <- iota 0 n, s <- words n k'] else [:: [::]].

Lemma mem_words n s : all (gtn n) s -> s \in words n (size s).
Proof.
elim: s => //= x s IH /andP[xn /IH s_in]; apply/allpairsP; exists (x, s).
by rewrite mem_iota.
Qed.

(** For each choice [s] of a perfect matching in each copy, a class is missed. *)
Lemma class_missed : all (fun s => has (fun i =>
  all (fun k => (class k == i) ==> (pm k != nth 0 s (copy k))) (iota 0 30)) (iota 0 6)) (words 3 5).
Proof. by vm_compute. Qed.

Section Matching.

Variable M : {set {set H}}.
Hypothesis matM : matching M.

(** The perfect matching of copy [i] which contains the edges of [M]. *)
Definition choice (i : nat) : nat :=
  if [pick k | (edge k \in M) && (copy k == i)] is Some k then pm k else 0.

Lemma same_matching k : edge k \in M -> pm k = choice (copy k).
Proof.
rewrite /choice => kM; case: pickP => [l /andP[lM /eqP lk]|/(_ k)]; last by rewrite kM eqxx.
apply/eqP/negPn/negP => ne; have [x [xk xl]] := edge_meet (esym lk) ne.
by rewrite (edge_inj (matM.2 _ _ kM lM x xk xl)) eqxx in ne.
Qed.

Lemma not_meet : exists i, M :&: E i = set0.
Proof.
pose s := map choice (iota 0 5).
have s_in : s \in words 3 5.
  rewrite (_ : 5 = size s) //; apply: mem_words; apply/allP => _ /mapP[i _ ->].
  rewrite /choice; case: pickP => // k _; exact: (ord_all k (P := fun k => pm k < 3)).
have /hasP[i] := allP class_missed s s_in; rewrite mem_iota => i6 /allP no.
exists (Ordinal i6); apply/setP => e; rewrite !inE; apply/negbTE/andP => -[eM].
case/imsetP=> k; rewrite inE => ki ek; rewrite {}ek in eM.
have k30 : val k \in iota 0 30 by rewrite mem_iota ltn_ord.
have k5 : copy k < 5 by apply: (ord_all k (P := fun k => copy k < 5)).
by have := no k k30; rewrite ki (same_matching eM) (nth_map 0) ?size_iota // nth_iota // eqxx.
Qed.

End Matching.

Theorem disproof : ~ AX_fair_representation_matching_delta_plus_2.
Proof.
move=> /(_ 6 H E H_partition)[M [matM meet]]; have [i Mi] := not_meet matM.
have := meet i; rewrite Mi cards0 leqNgt divn_gt0 ?addn2 // card_E.
by rewrite !ltnS Delta_H.
Qed.
