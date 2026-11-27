(** * Colouring degenerate graphs

    A [k]-degenerate graph is [(k+1)]-colourable: colour greedily along a degeneracy order
    [degenerate_chi_le].  Hence a graph of chromatic number greater than [k] has a nonempty set
    of vertices that induces a subgraph of minimum degree at least [k] (G. Szekeres and
    H. S. Wilf, 1968) [chi_min_degree_subgraph]. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc chromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** If the subgraph induced by [W] is [k]-degenerate, it has a proper colouring with [k.+1]
    colours. *)
Lemma degenerate_on_coloring (G : sgraph) (W : {set G}) (k : nat) :
  degenerate_on W k -> exists col : G -> 'I_k.+1, {in W &, forall x y, x -- y -> col x != col y}.
Proof.
have [n] := ubnP #|W|; elim: n W => // n IH W; rewrite ltnS => Wn degW.
have [->|W0] := eqVneq W set0; first by exists (fun=> ord0) => x; rewrite inE.
have [v [vW dv]] := degW W (subxx _) W0.
have [||col colP] := IH (W :\ v).
- by move: Wn; rewrite (cardsD1 v) vW.
- by move=> S SW; apply: degW; exact: subset_trans SW (subsetDl _ _).
have /subsetPn[c _ cN] : ~~ ([set: 'I_k.+1] \subset col @: (N(v) :&: W)).
  apply/negP => /subset_leq_card; rewrite cardsT card_ord; apply/negP; rewrite -ltnNge ltnS.
  exact: leq_trans (leq_imset_card _ _) dv.
have new y : y \in W -> v -- y -> c != col y.
  by move=> yW vy; apply: contraNneq cN => ->; apply: imset_f; rewrite !inE vy.
exists (fun x => if x == v then c else col x) => x y xW yW xy.
have [xv|xv] := eqVneq x v; have [yv|yv] := eqVneq y v.
- by rewrite xv yv sg_irrefl in xy.
- by apply: new; rewrite // -xv.
- by rewrite eq_sym; apply: new; rewrite // -yv sg_sym.
- by apply: colP; rewrite // !inE ?xv ?yv.
Qed.

(** A [k]-degenerate graph has chromatic number at most [k.+1]. *)
Lemma degenerate_chi_le (G : sgraph) (k : nat) : degenerate G k -> χ([set: G]) <= k.+1.
Proof.
move=> /degenerate_on_coloring[col colP]; apply/chi_leP; exists col.
by apply/proper_coloringP => x y; apply: colP; rewrite inE.
Qed.

(** A graph of chromatic number greater than [k] has a nonempty set of vertices that induces a
    subgraph of minimum degree at least [k]. *)
Lemma chi_min_degree_subgraph (G : sgraph) (k : nat) : 0 < k -> k < χ([set: G]) ->
  exists S : {set G}, S != set0 /\ min_degree_ge (induced S) k.
Proof.
case: k => // k _ ltk.
have [/existsP[S /andP[S0 /forall_inP degS]]|/existsPn noS] :=
  boolP [exists S : {set G}, (S != set0) && [forall v in S, k < #|N(v) :&: S|]]; last first.
  suff /degenerate_chi_le : degenerate G k by rewrite leqNgt ltk.
  move=> S _ S0; move: (noS S); rewrite S0 negb_forall_in => /exists_inP[v vS].
  by rewrite -leqNgt; exists v.
exists S; split=> // x; apply: leq_trans (degS _ (valP x)) _.
apply: leq_trans (subset_leq_card _) (leq_imset_card val (N(x))).
apply/subsetP => u /setIP[]; rewrite in_opn => xu uS; apply/imsetP.
by exists (Sub u uS); rewrite ?inE.
Qed.
