(** * Directed forcing conjecture

Fox, Himwich, Mani, Zhou, "A note on directed analogues of the Sidorenko and forcing conjectures",
arXiv:2210.16971, Conjecture 1.7 (2210.16971__01).

The homomorphism density t(B,D) of a digraph B in a digraph D is the fraction of the maps from
V(B) to V(D) that are homomorphisms (they send arcs to arcs).  Let K be the digraph with two
vertices and one arc.  The step function W_D of D on [0,1]^2 is 1 on I_x * I_y if xy is an arc
and 0 elsewhere, where the I_x are the intervals of length 1/|V(D)| indexed by the vertices.  The
cut norm of a function W on [0,1]^2 is the supremum of |int_(S*T) W| over measurable sets S, T.
An oriented graph B has the directed forcing property if, for every p in [0,1] and every sequence
(G_n) of oriented graphs with t(K,G_n) -> p/2 and t(B,G_n) -> (p/2)^e(B), where e(B) is the
number of arcs of B, the cut norm of W_(G_n) - p/2 tends to 0 ((G_n) is quasirandom).

Conjecture 1.7: if B is an oriented graph with a homomorphism to K and whose underlying undirected
graph has a cycle, then B has the directed forcing property.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Oriented graphs are those without digon (nor loop).  Densities are rational
numbers, and the graphs G_n are nonempty.  The cut norm of W_D - c is the maximum, over sets S, T
of vertices, of |a(S,T) - c |S| |T|| / |V(D)|^2, where a(S,T) is the number of arcs from S to T:
the integral is bilinear in the measures of the sets S /\ I_x and T /\ I_y, so its extrema are
attained when these are 0 or 1/|V(D)|.  The real number p is eliminated: t(K,G_n) converges if
and only if it is a Cauchy sequence, and then t(B,G_n) -> (p/2)^e(B) means
t(B,G_n) - t(K,G_n)^e(B) -> 0, and the constant p/2 of the cut norm can be replaced by t(K,G_n).
The statement below is thus equivalent to the conjecture. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** The underlying simple graph of [D]: arcs without direction, loops ignored. *)
Definition underlying (D : diGraph) : sgraph := sgraph_of_rel (@edge_rel D).

(** ** Definitions specific to the conjecture *)

(** The digraph with two vertices ([false] and [true]) and one arc, from [false] to [true]. *)
Definition single_arc : diGraph := DiGraph [rel x y : bool | ~~ x && y].

(** The arc density t(K,D) of [D]: arcs divided by |V(D)|^2. *)
Definition arc_density (D : diGraph) : rat := ((num_edges D)%:R / (#|D| ^ 2)%:R)%R.

(** The homomorphism density t(B,D) of [B] in [D]. *)
Definition hom_density (B D : diGraph) : rat := ((hom_count B D)%:R / (#|D| ^ #|B|)%:R)%R.

(** The number of arcs from [S] to [T]. *)
Definition arcs_between (D : diGraph) (S T : {set D}) : nat :=
  #|[set x : D * D | [&& x.1 \in S, x.2 \in T & x.1 -- x.2]]|.

(** The cut norm of W_D - c. *)
Definition cut_deviation (D : diGraph) (c : rat) : rat :=
  (\big[Num.max/0]_(S : {set D}) \big[Num.max/0]_(T : {set D})
     (`|(arcs_between S T)%:R - c * (#|S| * #|T|)%:R| / (#|D| ^ 2)%:R))%R.

(** The sequence [u] tends to 0. *)
Definition tends_to_zero (u : nat -> rat) : Prop :=
  forall eps : rat, (0 < eps)%R -> eventually (fun n => (`|u n| < eps)%R).

(** The sequence [u] is a Cauchy sequence. *)
Definition cauchy (u : nat -> rat) : Prop :=
  forall eps : rat, (0 < eps)%R ->
    eventually (fun m => forall n : nat, m <= n -> (`|u n - u m| < eps)%R).

(** [B] has the directed forcing property: a sequence of nonempty oriented graphs whose arc
    densities converge and whose [B]-densities are asymptotically those of a random orientation
    of a random graph of the same density is quasirandom. *)
Definition directed_forcing (B : diGraph) : Prop :=
  forall G : nat -> diGraph,
    (forall n : nat, oriented (G n)) ->
    (forall n : nat, 0 < #|G n|) ->
    cauchy (fun n => arc_density (G n)) ->
    tends_to_zero (fun n => hom_density B (G n) - arc_density (G n) ^+ num_edges B)%R ->
    tends_to_zero (fun n => cut_deviation (G n) (arc_density (G n))).

(** ** Statement *)

Definition AX_directed_sidorenko_forcing_cycle_homomorphism : Prop :=
  forall B : diGraph,
    oriented B ->
    homs_to B single_arc ->
    ~ is_forest [set: underlying B] ->
    directed_forcing B.
