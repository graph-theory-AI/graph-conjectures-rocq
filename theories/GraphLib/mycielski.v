(** * The Mycielski construction

    The Mycielskian of [G] consists of a copy of [G], a stable set formed by a shadow of each
    vertex of [G], adjacent to the copies of its neighbours, and a root adjacent to the shadows.
    If [G] is nonempty, its clique number is that of [G] (but at least 2), and its chromatic
    number is that of [G] plus one. *)

From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Mycielski.
Variable G : sgraph.

(** [Some (inl v)] is the copy of [v], [Some (inr v)] its shadow, and [None] the root. *)
Definition mycielski_rel : rel (option (G + G)) := fun x y =>
  match x, y with
  | Some (inl u), Some (inl v) | Some (inl u), Some (inr v) | Some (inr u), Some (inl v) => u -- v
  | Some (inr _), None | None, Some (inr _) => true
  | _, _ => false
  end.

Lemma mycielski_sym : symmetric mycielski_rel.
Proof. by move=> [[u|u]|] [[v|v]|] //=; rewrite sgP. Qed.

Lemma mycielski_irrefl : irreflexive mycielski_rel.
Proof. by move=> [[u|u]|] //=; rewrite sgP. Qed.

(** The Mycielskian of [G]. *)
Definition mycielski : sgraph := SGraph mycielski_sym mycielski_irrefl.

Definition mycielski_copy (v : G) : mycielski := Some (inl v).
Definition mycielski_shadow (v : G) : mycielski := Some (inr v).
Definition mycielski_root : mycielski := None.

Local Abbreviation copy := mycielski_copy.
Local Abbreviation shadow := mycielski_shadow.
Local Abbreviation root := mycielski_root.

Lemma mycielski_copy_inj : injective copy.
Proof. by move=> x y []. Qed.

Lemma stable_mycielski_shadow : stable [set shadow x | x : G].
Proof. by apply/stableP => _ _ /imsetP[x _ ->] /imsetP[y _ ->]. Qed.

(** When a clique or a stable set containing the root is removed, there remains an induced copy of
    [G], where the removed vertices are replaced by their shadows. *)
Lemma mycielski_avoid (C : {set mycielski}) :
  root \in C -> clique C \/ stable C ->
  exists i : G ⇀ mycielski, forall x : G, i x \notin C.
Proof.
move=> rC [clC|/stableP stC].
- exists (ISubgraph mycielski_copy_inj (fun x y => erefl)) => x.
  by apply/negP => /(clC root _ rC)/(_ isT).
- pose i x := if copy x \in C then shadow x else copy x.
  have i_inj : injective i by move=> x y; rewrite /i; do 2!case: ifP => _; case.
  have i_mono : {mono i : x y / x -- y}.
    move=> x y; rewrite /i; case: ifP => xC; case: ifP => yC //.
    by apply/esym/negbTE/(stC (copy x) (copy y)).
  exists (ISubgraph i_inj i_mono) => x /=; rewrite /i; case: ifP => [_|->//].
  by apply/negP => /(stC root _ rC)/negP[].
Qed.

(** [G] is nonempty. *)
Variable x0 : G.

Lemma omega_mycielski : ω([set: mycielski]) = maxn 2 (ω([set: G])).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: omegaP => K /maxclique_clique clK; have [rK|rK] := boolP (root \in K).
  + rewrite (leq_trans _ (leq_maxl _ _)) // (cardsD1 root) rK ltnS.
    apply: leq_trans (cliqueIstable clK stable_mycielski_shadow).
    rewrite subset_leq_card //; apply/subsetP => y /setD1P[yr yK]; rewrite inE yK /=.
    have: root -- y by apply: clK => //; rewrite eq_sym.
    by case: y {yr yK} => [[]|] // v _; apply: imset_f.
  + pose proj (x : mycielski) :=
      match x with Some (inl v) | Some (inr v) => v | None => x0 end.
    have proj_edge : {in K &, forall x y, x != y -> proj x -- proj y}.
      move=> x y xK yK /(clK _ _ xK yK).
      case: x xK => [[u|u]|] xK; case: y yK => [[v|v]|] yK //; by case/negP: rK.
    have proj_inj : {in K &, injective proj}.
      move=> x y xK yK eq_xy; apply: contraFeq (sg_irrefl (proj y)) => /(proj_edge _ _ xK yK).
      by rewrite eq_xy.
    have clPK : clique (proj @: K).
      move=> _ _ /imsetP[x xK ->] /imsetP[y yK ->] neq_xy; apply: proj_edge => //.
      by apply: contraNneq neq_xy => ->.
    rewrite (leq_trans _ (leq_maxr _ _)) // -(card_in_imset proj_inj) clique_bound //.
    by rewrite inE subsetT; apply/cliqueP.
- rewrite geq_max; apply/andP; split.
  + have clS : clique [set root; shadow x0] by apply: clique2.
    rewrite -(cards2 root (shadow x0)).
    apply: clique_bound; rewrite inE subsetT; exact/cliqueP.
  + rewrite (omega_isubgraph (ISubgraph mycielski_copy_inj (fun x y => erefl))).
    exact/sub_omega/subsetT.
Qed.

Theorem chi_mycielski : χ([set: mycielski]) = (χ([set: G])).+1.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have /chi_leP[col /proper_coloringP pcol] := leqnn χ([set: G]); apply/chi_leP.
  pose ext (x : mycielski) :=
    match x with
    | Some (inl v) => lift ord0 (col v)
    | Some (inr _) => ord0
    | None => lift ord0 (col x0)
    end.
  exists ext; apply/proper_coloringP => - [[u|u]|] [[v|v]|] //=; rewrite (inj_eq lift_inj).
  exact: pcol.
- case: (chiP [set: mycielski]) => P colP _; have /andP[partP /forall_inP/= stabP] := colP.
  have rP : root \in cover P by rewrite (cover_partition partP).
  have [|//|i iC] := @mycielski_avoid (pblock P root).
  + by rewrite mem_pblock.
  + by right; apply/stabP/pblock_mem.
  rewrite (cardsD1 (pblock P root)) pblock_mem // ltnS (chi_isubgraph i).
  apply: leq_trans (color_bound (coloringD1 colP (pblock_mem rP))).
  by apply/sub_chi/subsetP => _ /imsetP[x _ ->]; rewrite !inE iC.
Qed.

End Mycielski.
