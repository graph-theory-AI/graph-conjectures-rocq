(** * A K_5-free graph with ζ(G) = k and χ(G) = k + 3

    A cocolouring is a colouring whose classes are cliques or stable sets.  The complement of the
    circulant graph C_13(1, 5) has ω <= 4, ζ = 4 and χ = 7.  The Mycielski construction preserves
    ω <= 4 and adds 1 to χ; it also adds 1 to ζ when there is an optimal cocolouring with a stable
    class, and then the new graph has one too.  The graph is obtained by k - 4 iterations of this
    construction.

    The proof comes from Graph-Theory-LLM-Proofs (attacks/2408.02400__00).  It was formalized
    in graph-theory-rocq (chromatic-theory/theories/applications/cochromatic_gap). *)

From GraphTheory Require Import digraph sgraph dom coloring.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic mycielski.
From GC.chromatic.AX_chromatic_cochromatic_gap_three_small_clique Require main.
From GC.chromatic.AX_chromatic_cochromatic_gap_three_small_clique Require Import seed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Cocolourings of the Mycielskian *)

(** Removing the class of the root leaves a copy of [G]. *)
Lemma cocolorable_mycielski (G : sgraph) (k : nat) :
  cocolorable (mycielski G) k.+1 -> cocolorable G k.
Proof.
move=> [col hom]; pose c := col (mycielski_root G).
have [|i iC] := mycielski_avoid _ (hom c); first by rewrite inE.
have colP x : {j | col (i x) = lift c j}.
  by have := iC x; rewrite inE eq_sym => /unlift_some[j eq_j _]; exists j.
exists (fun x => sval (colP x)) => j.
have classE : i @: [set x | sval (colP x) == j] \subset [set v | col v == lift c j].
  apply/subsetP => _ /imsetP[x + ->]; rewrite !inE => /eqP<-.
  exact/eqP/(svalP (colP x)).
have [cl|st] := hom (lift c j); [left|right].
- by apply/cliqueP; rewrite (cliqueb_isubgraph i); apply/cliqueP/(sub_clique classE).
- by rewrite (stable_isubgraph i) (sub_stable classE).
Qed.

(** [G] has a cocolouring with [k.+1] colours, and the class of [ord0] is stable. *)
Definition stable_cocolorable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> 'I_k.+1,
    (forall i, clique [set v | col v == i] \/ stable [set v | col v == i]) /\
    stable [set v | col v == ord0].

(** The shadows receive the new colour, and the root the stable colour of [G]. *)
Lemma stable_cocolorable_mycielski (G : sgraph) (k : nat) :
  stable_cocolorable G k -> stable_cocolorable (mycielski G) k.+1.
Proof.
move=> [col [hom st0]].
pose ext (x : mycielski G) : 'I_k.+2 :=
  match x with
  | Some (inl v) => lift ord0 (col v)
  | Some (inr _) => ord0
  | None => lift ord0 ord0
  end.
have st_ext0 : stable [set v | ext v == ord0].
  by apply/stableP => - [[u|u]|] [[v|v]|]; rewrite !inE.
exists ext; split=> // i; case: (unliftP ord0 i) => [j ->|->]; last by right.
have {hom st0} [/stableP st|[j0 cl]] : stable [set v | col v == j] \/
    j != ord0 /\ clique [set v | col v == j].
  by have [->|] := eqVneq j ord0; [left|case: (hom j); [right|left]].
- right; apply/stableP => - [[u|u]|] [[v|v]|]; rewrite !inE //= !(inj_eq lift_inj).
  by move=> cu cv; apply: st; rewrite inE.
- left=> - [[u|u]|] [[v|v]|]; rewrite !inE //= !(inj_eq lift_inj) ?[ord0 == j]eq_sym;
    rewrite ?(negbTE j0) //.
  by move=> cu cv neq_uv; apply: cl; rewrite ?inE.
Qed.

(** ** The iterated construction *)

Fixpoint gap_graph (n : nat) : sgraph :=
  if n is n'.+1 then mycielski (gap_graph n') else seed.

Definition gap_graph_vertex (n : nat) : gap_graph n :=
  if n is n'.+1 then mycielski_root (gap_graph n') else (ord0 : seed).

Lemma omega_gap_graph (n : nat) : ω([set: gap_graph n]) <= 4.
Proof.
elim: n => [|n IHn] /=; first exact: omega_seed.
by rewrite (omega_mycielski (gap_graph_vertex n)) geq_max.
Qed.

Lemma chi_gap_graph (n : nat) : χ([set: gap_graph n]) = n + 7.
Proof.
elim: n => [|n IHn] /=; first exact: chi_seed.
by rewrite (chi_mycielski (gap_graph_vertex n)) IHn.
Qed.

Lemma cochromatic_gap_graph (n : nat) : cochromatic_number (gap_graph n) (n + 4).
Proof.
split=> [|k].
- suff [col [hom _]] : stable_cocolorable (gap_graph n) (n + 3) by rewrite addnS; exists col.
  elim: n => [|n IHn]; first exact: seed_cocoloring.
  exact: stable_cocolorable_mycielski.
- elim: n k => [|n IHn] k; first exact: cocolorable_seed_ge.
  case: k => [[col _]|k /cocolorable_mycielski]; last exact: IHn.
  by case: (col (gap_graph_vertex n.+1)).
Qed.

Lemma gap_three : main.AX_chromatic_cochromatic_gap_three_small_clique.
Proof.
move=> k lt4k; exists (gap_graph (k - 4)); rewrite ltnS omega_gap_graph chi_gap_graph.
have eq_k : k - 4 + 4 = k by rewrite subnK // ltnW.
split=> //; first by have := cochromatic_gap_graph (k - 4); rewrite eq_k.
by rewrite (addnA _ 4 3) eq_k.
Qed.
