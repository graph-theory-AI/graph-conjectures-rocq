(** * The list edge colouring conjecture implies R_l(K_{1,2}, k) = k + 2 for odd k

A colouring of the edges of K_n has no monochromatic K_{1,2} if and only if it is proper.  Let k be
odd.  In K_{k+2}, the k + 1 edges at a vertex coloured from the same k colours contain two edges of
the same colour.  Conversely, for n <= k + 1, the edge chromatic number of K_n is at most k (the
round-robin colouring of K_{k+1}: the edge ij gets the colour i + j mod k, where the vertex k is
replaced by the other end; at each vertex the colours are distinct because 2 is invertible
modulo k).  By the list edge colouring conjecture, the line graph of K_n is then k-choosable, and
every assignment of lists of k colours to the edges of K_n has a proper colouring.

The implication is the edge e039 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_X219.v), with the
conclusion stated as the (n-1)-edge-choosability of K_n for even n. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc chromatic.
From GC.chromatic.OPG_list_edge_chromatic_equals_edge_chromatic Require Import
  main(OPG_list_edge_chromatic_equals_edge_chromatic).
From GC.chromatic.AX_list_ramsey_k12_odd_k Require Import main(AX_list_ramsey_k12_odd_k).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The complete graph as a multigraph, and its round-robin edge colouring *)

Section CompleteMultigraph.
Variable n : nat.

(** The edges of K_n are the pairs [(i, j)] with [i < j]. *)
Definition kn_edge := {p : 'I_n * 'I_n | p.1 < p.2}.

Definition kn_mgraph : mgraph :=
  @Graph unit unit 'I_n kn_edge (fun b e => if b then (val e).2 else (val e).1)
    (fun _ => tt) (fun _ => tt).

Lemma kn_loopless : mloopless kn_mgraph.
Proof. by case=> -[i j] /= ij; rewrite /= neq_ltn ij. Qed.

(** The ends of an edge. *)
Definition kn_ends (e : edge kn_mgraph) : {set 'I_n} := [set (val e).1; (val e).2].

Lemma kn_incident (x : kn_mgraph) e : incident x e = (x \in kn_ends e).
Proof.
rewrite /incident !inE.
by apply/existsP/orP => [[[] /eqP <-]|[] /eqP ->]; [right|left|exists false|exists true].
Qed.

Lemma kn_ends_ex (u v : 'I_n) : u != v -> exists e, kn_ends e = [set u; v].
Proof.
case: (ltngtP u v) => [uv|vu|/val_inj ->]; last by rewrite eqxx.
- by exists (exist _ (u, v) uv).
- by exists (exist _ (v, u) vu); rewrite /kn_ends setUC.
Qed.

End CompleteMultigraph.

Section RoundRobin.
Variable k : nat.
Hypothesis k_odd : odd k.

(** The colour of the edge [xy] of K_{k+1}: [x + y] modulo [k], where the vertex [k] is replaced
    by the other end. *)
Definition rr (x y : nat) : nat := ((if x == k then y else x) + (if y == k then x else y)) %% k.

Lemma rrC x y : rr x y = rr y x.
Proof. by rewrite /rr addnC. Qed.

Lemma rr_lt x y : rr x y < k.
Proof. exact: ltn_pmod (odd_gt0 k_odd). Qed.

Lemma dbl_mod_inj a b : a < k -> b < k -> (a + a) %% k = (b + b) %% k -> a = b.
Proof.
move=> ak bk E; rewrite -(modn_small ak) -(modn_small bk).
have kE : k = (k./2).*2.+1 by rewrite -[LHS](odd_double_half k) k_odd.
have h x : (k./2.+1 * (x + x)) %% k = x %% k.
  by rewrite addnn -mul2n mulnA muln2 doubleS -kE mulSnr mulnC modnMDl.
by rewrite -h -modnMmr E modnMmr h.
Qed.

(** At a vertex [v], the colours of the edges are distinct. *)
Lemma rr_inj v u1 u2 : v <= k -> u1 <= k -> u2 <= k -> u1 != v -> u2 != v ->
  rr v u1 = rr v u2 -> u1 = u2.
Proof.
move=> vk u1k u2k u1v u2v; rewrite /rr.
have lt u : u <= k -> u != k -> u < k by rewrite ltn_neqAle => -> ->.
case: (v =P k) => [vE|/eqP vk'].
  move: u1v u2v; rewrite vE => u1v u2v; rewrite (negbTE u1v) (negbTE u2v).
  by apply: dbl_mod_inj; apply: lt.
have vlt := lt v vk vk'.
case: (u1 =P k) => [->|/eqP u1k']; case: (u2 =P k) => [->|/eqP u2k'] // /eqP;
  rewrite eqn_modDl !modn_small ?lt // => /eqP E.
- by rewrite E eqxx in u2v.
- by rewrite E eqxx in u1v.
- by [].
Qed.

(** The round-robin colouring is a proper colouring of the edges of K_n for [n <= k + 1]. *)
Lemma kn_chi_line n : n <= k.+1 -> χ([set: mline_graph (kn_mgraph n)]) <= k.
Proof.
move=> nk; apply/chi_leP.
exists (fun e : mline_graph (kn_mgraph n) => Ordinal (rr_lt (val e).1 (val e).2)).
have R (x y z : 'I_n) : y != x -> z != x -> rr x y = rr x z -> y = z :> nat.
  by apply: rr_inj; apply: leq_trans (ltn_ord _) nk.
apply/proper_coloringP => -[[a b] /= ab] [[c d] /= cd] /andP[ne /existsP[v]].
rewrite !kn_incident /kn_ends !inE /= => /andP[].
move=> /orP[]/eqP-> /orP[]/eqP vE; subst; apply: contraNneq ne => /(congr1 val) /= E.
- have /val_inj bd := R _ _ _ (negbT (gtn_eqF ab)) (negbT (gtn_eqF cd)) E.
  by subst; rewrite (bool_irrelevance ab cd).
- rewrite [rr c d]rrC in E; have bc := R _ _ _ (negbT (gtn_eqF ab)) (negbT (ltn_eqF cd)) E.
  by move: (ltn_trans cd ab); rewrite bc ltnn.
- rewrite rrC in E; have ad := R _ _ _ (negbT (ltn_eqF ab)) (negbT (gtn_eqF cd)) E.
  by move: (ltn_trans ab cd); rewrite ad ltnn.
- rewrite rrC [rr c d]rrC in E.
  have /val_inj ac := R _ _ _ (negbT (ltn_eqF ab)) (negbT (ltn_eqF cd)) E.
  by subst; rewrite (bool_irrelevance ab cd).
Qed.

End RoundRobin.

(** ** List Ramsey numbers of K_{1,2} *)

Abbreviation list_ramsey_arrows := GC.chromatic.AX_list_ramsey_k12_odd_k.main.list_ramsey_arrows.

(** With the same list of [k] colours on all edges of K_{k+2}, two edges at a vertex have the same
    colour. *)
Lemma list_ramsey_arrows_K12 k : list_ramsey_arrows 'K_k.+2 k 'K_1,2.
Proof.
exists 'I_k, (fun=> setT); split=> [e|col _]; first by rewrite cardsT card_ord.
pose f (j : 'I_k.+1) := col [set ord0; lift ord0 j].
have /injectivePn[x [y xy fxy]] : ~~ injectiveb f.
  by apply/injectiveP => /leq_card; rewrite !card_ord ltnn.
exists (f x),
  (fun z : 'K_1,2 => if z is inr i then lift ord0 (if i == ord0 then x else y) else ord0).
- move=> [i|i] [j|j] /= => [_|/eqP|/esym/eqP|/lift_inj];
    rewrite ?(negbTE (neq_lift _ _)) ?(ord1 i) ?(ord1 j) //.
  by case: i j => -[|[|//]] ? [[|[|//]] ?] /= E; try (by congr inr; apply: val_inj);
    rewrite E eqxx in xy.
- move=> [i|i] [j|j] //= _ _; rewrite edge_color_classE /=; last rewrite setUC.
  all: by case: ifP => _; rewrite -/(f x) -/(f y) ?fxy.
Qed.

(** Below k + 2 vertices, under the list edge colouring conjecture, the lists of [k] colours on
    the edges have a proper colouring. *)
Lemma list_ramsey_not_arrows_K12 k m : OPG_list_edge_chromatic_equals_edge_chromatic ->
  odd k -> m <= k.+1 -> ~ list_ramsey_arrows 'K_m k 'K_1,2.
Proof.
move=> lecc ok mk [C [L [Lk mono]]].
apply: (@choice_number_nn (mline_graph (kn_mgraph m))) => -[ch chn].
have chk : choosable (mline_graph (kn_mgraph m)) k.
  apply: choosable_leq chn.1; rewrite (lecc _ _ (@kn_loopless m) chn); exact: kn_chi_line.
have [f [fL fP]] := chk C (fun e => L (kn_ends e)) (fun e => eq_leq (esym (Lk _))).
have Lne S : exists c, c \in L S by apply/set0Pn; rewrite -card_gt0 Lk odd_gt0.
pose c' S := if [pick e | kn_ends e == S] is Some e then f e else xchoose (Lne S).
have [|c [h hinj hhom]] := mono c'.
  by move=> S; rewrite /c'; case: pickP => [e /eqP <-|_]; [exact: fL | exact: xchooseP].
have c'E u v : u != v -> exists2 e, kn_ends e = [set u; v] & c' [set u; v] = f e.
  move=> uv; rewrite /c'; case: pickP => [e /eqP E|none]; first by exists e.
  by case: (kn_ends_ex uv) => e /eqP; rewrite none.
pose a : 'K_1,2 := inl ord0.
have edge z : a -- z -> exists2 e, kn_ends e = [set h a; h z] & f e = c.
  move=> az; have ne : h a != h z by apply: contraTneq az => /hinj <-; rewrite sg_irrefl.
  have := hhom _ _ az ne; rewrite edge_color_classE => /andP[_ /eqP <-].
  by have [e E1 E2] := c'E _ _ ne; exists e.
have [e1 E1 f1] := edge (inr ord0) isT; have [e2 E2 f2] := edge (inr ord_max) isT.
have : (e1 : mline_graph (kn_mgraph m)) -- e2.
  apply/andP; split; last by apply/existsP; exists (h a); rewrite !kn_incident E1 E2 !inE eqxx.
  apply/eqP => e12; have : h (inr ord_max) \in kn_ends e1 by rewrite e12 E2 !inE eqxx orbT.
  by rewrite E1 !inE => /orP[]/eqP/hinj // -[/(congr1 val)].
by move/fP; rewrite f1 f2 eqxx.
Qed.

Theorem OPG_list_edge_chromatic_equals_edge_chromatic_implies_AX_list_ramsey_k12_odd_k :
  OPG_list_edge_chromatic_equals_edge_chromatic -> AX_list_ramsey_k12_odd_k.
Proof.
move=> lecc k ok; rewrite addn2; split=> [|m]; first exact: list_ramsey_arrows_K12.
by rewrite ltnS; apply: list_ramsey_not_arrows_K12.
Qed.

Check (OPG_list_edge_chromatic_equals_edge_chromatic_implies_AX_list_ramsey_k12_odd_k :
  GC.chromatic.OPG_list_edge_chromatic_equals_edge_chromatic.main.OPG_list_edge_chromatic_equals_edge_chromatic ->
  GC.chromatic.AX_list_ramsey_k12_odd_k.main.AX_list_ramsey_k12_odd_k).

Print Assumptions OPG_list_edge_chromatic_equals_edge_chromatic_implies_AX_list_ramsey_k12_odd_k.
