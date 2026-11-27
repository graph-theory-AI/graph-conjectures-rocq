(** * Total (Δ+2)-choosability implies the total colouring conjecture

Let G be a nonempty multigraph without loops and parallel edges, and S its underlying simple graph
(the skeleton).  Sending a vertex to itself and an edge to the pair of its ends maps the total graph
of G into the total graph of S, preserving adjacency (distinct edges have distinct pairs of ends).
A total colouring of S from constant lists of Δ(S) + 2 colours thus gives a total colouring of G
with Δ(S) + 2 <= Δ(G) + 2 colours.  Conversely, a vertex of maximum degree and its Δ(G) incident
edges form a clique of the total graph, so at least Δ(G) + 1 colours are needed.

The implication is the edge e002 of relations.json in graph-conjectures.  It was formalized in
graph-theory-rocq (chromatic-theory/theories/conjectures/implications_U5.v). *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.
From GC.GraphLib Require Import chromatic(chi_leP, proper_coloringP).
From GC.chromatic.AX_list_total_coloring_delta_plus_2 Require Import
  main(AX_list_total_coloring_delta_plus_2).
From GC.chromatic.OPG_total_coloring_max_degree_plus_2 Require Import
  main(OPG_total_coloring_max_degree_plus_2).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation Delta := GC.chromatic.AX_list_total_coloring_delta_plus_2.main.Delta.
Abbreviation total_graph := GC.chromatic.AX_list_total_coloring_delta_plus_2.main.total_graph.
Abbreviation mgraph := GC.chromatic.OPG_total_coloring_max_degree_plus_2.main.mgraph.
Abbreviation mDelta := GC.chromatic.OPG_total_coloring_max_degree_plus_2.main.mDelta.
Abbreviation msimple := GC.chromatic.OPG_total_coloring_max_degree_plus_2.main.msimple.
Abbreviation mtotal_graph := GC.chromatic.OPG_total_coloring_max_degree_plus_2.main.mtotal_graph.

Section Bridge.
Variable G : mgraph.
Abbreviation SG := (skeleton.skeleton G).

Lemma incident_ends (x : G) (e : edge G) : incident x e -> x \in [set source e; target e].
Proof. by case/existsP => -[] /eqP <-; rewrite !inE eqxx ?orbT. Qed.

(** The degree of a vertex of the skeleton is at most its number of incident edges. *)
Lemma Delta_skeleton : Delta SG <= mDelta G.
Proof.
apply/bigmax_leqP => x _; apply: leq_trans (@leq_bigmax G (fun v => #|edges_at v|) x).
pose other (e : edge G) := if source e == x then target e else source e.
apply: leq_trans (leq_imset_card other _); apply: subset_leq_card; apply/subsetP => y.
rewrite inE /= /skeleton.sk_rel => /andP[xy /existsP[e]]; rewrite !inE => exy.
apply/imsetP; exists e.
  by rewrite inE; case/orP: exy => /andP[] => [sx _|_ tx]; apply/existsP;
     [exists false | exists true].
by rewrite /other; case/orP: exy => /andP[/eqP-> /eqP->]; rewrite ?eqxx // eq_sym (negbTE xy).
Qed.

(** The lower bound: a vertex of maximum degree and its incident edges form a clique. *)
Lemma mtotal_chi_ge : 0 < #|G| -> (mDelta G).+1 <= χ([set: mtotal_graph G]).
Proof.
move=> G_gt0; have [v vmax] := @eq_bigmax G (fun u => #|edges_at u|) G_gt0.
rewrite /mDelta vmax.
pose K : {set mtotal_graph G} := inl v |: [set inr e | e in edges_at v].
have clK : clique K.
  move=> a b; rewrite !inE => /predU1P[->|/imsetP[e /[!inE] ev ->]]
    /predU1P[->|/imsetP[f /[!inE] fv ->]]; rewrite ?eqxx // => ef.
  apply/andP; split; first by apply: contra ef => /eqP->.
  by apply/existsP; exists v; rewrite ev fv.
have -> : (#|edges_at v|).+1 = #|K|.
  by rewrite cardsU1 card_imset ?(introN imsetP) // => [e f []|[]].
by rewrite -(chi_clique clK) sub_chi ?subsetT.
Qed.

Hypothesis simpleG : msimple G.

Lemma ends_edge (e : edge G) : [set source e; target e : SG] \in E(SG).
Proof.
by rewrite (@in_edges SG); apply/andP; split; [exact: simpleG.1 | exact: skeleton.adjacent_edge].
Qed.

(** Vertices to themselves, edges to the pairs of their ends. *)
Definition total_hom (a : mtotal_graph G) : total_graph SG :=
  match a with
  | inl x => inl x
  | inr e => inr (exist (fun s => s \in E(SG)) _ (ends_edge e))
  end.

Lemma total_hom_edge (a b : mtotal_graph G) : a -- b -> total_hom a -- total_hom b.
Proof.
case: a b => [x|e] [y|f] //=; try exact: incident_ends.
case/andP => ef /existsP[v /andP[ve vf]]; apply/andP; split.
  by apply: contra ef => /eqP/simpleG.2->.
by apply/set0Pn; exists v; rewrite inE !incident_ends.
Qed.

(** The upper bound: pull back a total colouring of the skeleton. *)
Lemma mtotal_chi_le :
  AX_list_total_coloring_delta_plus_2 -> χ([set: mtotal_graph G]) <= (mDelta G).+2.
Proof.
move=> X; pose k := Delta SG + 2.
have [|f [_ fP]] := X SG 'I_k (fun _ => setT); first by move=> _; rewrite cardsT card_ord.
apply: (@leq_trans k); last by rewrite /k addn2 !ltnS Delta_skeleton.
apply/chi_leP; exists (f \o total_hom); apply/proper_coloringP => a b ab.
exact: fP (total_hom_edge ab).
Qed.

End Bridge.

Theorem AX_list_total_coloring_delta_plus_2_implies_OPG_total_coloring_max_degree_plus_2 :
  AX_list_total_coloring_delta_plus_2 -> OPG_total_coloring_max_degree_plus_2.
Proof.
by move=> X G simpleG G_gt0; rewrite mtotal_chi_ge // mtotal_chi_le.
Qed.

Check (AX_list_total_coloring_delta_plus_2_implies_OPG_total_coloring_max_degree_plus_2 :
  GC.chromatic.AX_list_total_coloring_delta_plus_2.main.AX_list_total_coloring_delta_plus_2 ->
  GC.chromatic.OPG_total_coloring_max_degree_plus_2.main.OPG_total_coloring_max_degree_plus_2).
Print Assumptions
  AX_list_total_coloring_delta_plus_2_implies_OPG_total_coloring_max_degree_plus_2.
