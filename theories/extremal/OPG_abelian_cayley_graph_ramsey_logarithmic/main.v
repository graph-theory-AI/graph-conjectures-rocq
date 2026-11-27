(** * Ramsey properties of Cayley graphs of abelian groups

Alon; Problem BCC14.6 of the problem list of the British Combinatorial Conference; Open Problem
Garden, ramsey_properties_of_cayley_graphs.

Let S = -S be a subset of an abelian group G.  The Cayley graph of G and S has vertex set G, and
distinct vertices x and y are adjacent if y - x ∈ S.

Conjecture: there is a constant c such that every finite abelian group G has a subset S = -S such
that the Cayley graph of G and S has no clique and no stable set of size more than c log |G|.

Encoding.  Groups are written multiplicatively.  The trivial group is excluded, as log 1 = 0.  The
logarithm is in base 2 and c is a positive natural number, which is not a restriction.  The
inequality m <= c log |G| is written 2^m <= |G|^c.  The neutral element is ignored when it is in S,
so that Cayley graphs are simple. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring.
From mathcomp Require Import boot fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** ** Definitions copied from GraphLib/spectral.v *)

(** The (undirected) Cayley graph of the group [gT] for the connection set [S] (made symmetric,
    without the neutral element). *)
Definition cayley_graph (gT : finGroupType) (S : {set gT}) : sgraph :=
  sgraph_of_rel (fun x y : gT => (x^-1 * y)%g \in S).

(** ** Statement *)

Definition OPG_abelian_cayley_graph_ramsey_logarithmic : Prop :=
  exists c : nat, 0 < c /\
    forall gT : finGroupType, abelian [set: gT] -> 1 < #|gT| ->
      exists S : {set gT},
        (forall x : gT, (x \in S) = (x^-1 \in S)%g) /\
        2 ^ ω([set: cayley_graph S]) <= #|gT| ^ c /\
        2 ^ α([set: cayley_graph S]) <= #|gT| ^ c.
