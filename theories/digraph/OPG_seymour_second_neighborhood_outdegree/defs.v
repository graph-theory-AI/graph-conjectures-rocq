(** * Definitions for the proof of Seymour's second neighbourhood conjecture

Notions shared by the files of this directory, with their basic facts.

Provenance.  The proof follows the paper of OpenAI, "A proof of Seymour's second-neighborhood
conjecture" (September 23, 2026), a model-generated manuscript that is not peer reviewed,
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf
and is organized after its Lean formalization,
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood
(here: PruningDefinitions.lean, Basic.lean, Model.lean).  The Lean development proves the full
statement of the conjecture (the comparator challenge
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SeymourSecondNeighborhood.lean
states it for every nonempty finite oriented graph).

For a digraph [G] and [S : {set G}], the image F(S) of the paper (the union of the
out-neighbourhoods of the vertices of S, which may meet S) is [NS(S)] of GraphTheory.  Pairs of
vertices [z : G * G] are the points of the extremal argument (Section 4 of the paper): the left
image of a family [P] moves the first coordinate forward along an arc, the right image of a
family [Q] moves the second coordinate forward along an arc. *)

From GraphTheory Require Import digraph.
From GC.GraphLib Require digraph.
From GC.digraph.OPG_seymour_second_neighborhood_outdegree Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation oriented := main.oriented.
Abbreviation outdeg := main.outdeg.
Abbreviation second_outneigh := main.second_outneigh.
Abbreviation in_NS := GC.GraphLib.digraph.in_NS.
Abbreviation NS_sub := GC.GraphLib.digraph.NS_sub.
Abbreviation NSU := GC.GraphLib.digraph.NSU.

(** ** Vertices and sets of vertices *)

(** [v] satisfies the second neighbourhood inequality. *)
Definition good (D : diGraph) (v : D) : bool := outdeg v <= #|second_outneigh v|.

Section Growth.
Variable G : diGraph.

(** Every vertex has an in-neighbour. *)
Definition positive_indeg : Prop := forall v : G, exists u : G, u -- v.

(** Subset deficit (inequality (3) of the paper):
    |F^2(S) \ F(S)| < |F(S) \ S| for every nonempty proper set S. *)
Definition subset_deficit : Prop :=
  forall S : {set G}, S != set0 -> S != setT -> #|NS(NS(S)) :\: NS(S)| < #|NS(S) :\: S|.

(** Strict subset growth (inequality (2) of the paper):
    |U| + |F^2(U)| < 2 |F(U)| for every nonempty proper set U. *)
Definition strict_growth : Prop :=
  forall U : {set G}, U != set0 -> U != setT -> #|U| + #|NS(NS(U))| < 2 * #|NS(U)|.

End Growth.

(** ** Families of pairs *)

Section Pairs.
Variable G : diGraph.
Implicit Types (P Q R C : {set G * G}) (a b z : G * G).

(** Left image F_1(P): the points (i,j) such that (p,j) is in P for some arc p -> i. *)
Definition left_image P : {set G * G} :=
  [set z | [exists p, ((p, z.2) \in P) && (p -- z.1)]].

(** Right image F_2(Q): the points (i,j) such that (i,s) is in Q for some arc s -> j. *)
Definition right_image Q : {set G * G} :=
  [set z | [exists s, ((z.1, s) \in Q) && (s -- z.2)]].

(** The diagonal of G * G. *)
Definition diagonal : {set G * G} := [set z | z.1 == z.2].

(** A left member [a = (p,j)] and a right member [b = (i,s)] conflict when p -> i and s -> j. *)
Definition conflict a b : bool := (a.1 -- b.1) && (b.2 -- a.2).

(** A left member [a = (p,j)] covers the point [z] when z = (i,j) with p -> i. *)
Definition lcovers a z : bool := (a.2 == z.2) && (a.1 -- z.1).

(** A right member [b = (i,s)] covers the point [z] when z = (i,j) with s -> j. *)
Definition rcovers b z : bool := (b.1 == z.1) && (b.2 -- z.2).

(** No member of [R] conflicts with a member of [C]. *)
Definition conflict_free R C : bool := [forall a in R, forall b in C, ~~ conflict a b].

(** The corners (i,j) of the conflicts of [R] and [C] (the set Z of Lemma 3.1). *)
Definition Zset R C : {set G * G} := left_image R :&: right_image C.

(** The corners (p,s) of the conflicts of [R] and [C] (the set H of Lemma 3.1). *)
Definition Hset R C : {set G * G} :=
  [set h | [exists i, exists j, [&& (h.1, j) \in R, (i, h.2) \in C, (h.1 -- i) & h.2 -- j]]].

(** The conclusion of the pruning lemma (Lemma 3.1 of the paper) for subfamilies [R'] of [R]
    and [C'] of [C]: no conflict remains, initially conflict-free members are retained, and the
    number of deleted members is at most |H| plus the number of points of Z covered by no
    retained member.  ([[/\ ...]] has at most five components, hence the two inclusions in one
    boolean.) *)
Definition pruning_result R C R' C' : Prop :=
  [/\ (R' \subset R) && (C' \subset C), conflict_free R' C',
      {in R, forall a, [forall b in C, ~~ conflict a b] -> a \in R'},
      {in C, forall b, [forall a in R, ~~ conflict a b] -> b \in C'} &
      #|R :\: R'| + #|C :\: C'|
        <= #|Hset R C| + #|Zset R C :\: (left_image R' :|: right_image C')|].

(** The three relations of the augmented bipartite graph of the pruning lemma, between members
    of [R], members of [C] and points of [Zset R C]. *)
Definition orig_rel R C a b : bool := [&& a \in R, (b \in C) & conflict a b].
Definition alpha_rel R C z a : bool := [&& z \in Zset R C, (a \in R) & lcovers a z].
Definition beta_rel R C z b : bool := [&& z \in Zset R C, (b \in C) & rcovers b z].

End Pairs.

Section Facts.
Variable G : diGraph.
Implicit Types (P Q R C : {set G * G}) (a b z : G * G).

Lemma in_left_image P z : (z \in left_image P) = [exists p, ((p, z.2) \in P) && (p -- z.1)].
Proof. by rewrite inE. Qed.

Lemma in_right_image Q z : (z \in right_image Q) = [exists s, ((z.1, s) \in Q) && (s -- z.2)].
Proof. by rewrite inE. Qed.

Lemma conflict_freeP R C :
  reflect (forall a b, a \in R -> b \in C -> ~~ conflict a b) (conflict_free R C).
Proof.
apply: (iffP forall_inP) => [h a b aR bC|h a aR]; first exact: (forall_inP (h a aR)).
by apply/forall_inP => b; exact: h.
Qed.

(** The corners of a conflict. *)
Lemma conflict_Zset R C a b :
  a \in R -> b \in C -> conflict a b -> (b.1, a.2) \in Zset R C.
Proof.
case: a b => p j [i s] aR bC /andP[/= pi sj]; rewrite !inE /=.
by apply/andP; split; apply/existsP; [exists p | exists s]; apply/andP.
Qed.

(** Conflict-freeness is the disjointness of the left and right images. *)
Lemma conflict_free_disjoint R C :
  conflict_free R C = [disjoint left_image R & right_image C].
Proof.
rewrite -setI_eq0; apply/conflict_freeP/eqP => [h|h a b aR bC].
  apply/setP => -[i j]; rewrite !inE /=; apply/negP => /andP[].
  move=> /existsP[p /andP[pR pi]] /existsP[s /andP[sC sj]].
  by move: (h _ _ pR sC); rewrite /conflict pi sj.
by apply/negP => /(conflict_Zset aR bC); rewrite /Zset h inE.
Qed.

Lemma conflict_Hset R C a b :
  a \in R -> b \in C -> conflict a b -> (a.1, b.2) \in Hset R C.
Proof.
case: a b => p j [i s] aR bC /andP[/= pi sj]; rewrite inE /=.
by apply/existsP; exists i; apply/existsP; exists j; apply/and4P.
Qed.

End Facts.
