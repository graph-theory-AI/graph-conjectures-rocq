(** * The pentagon problem

Nešetřil, "Aspects of structural combinatorics (graph homomorphisms and their use)", Taiwanese J.
Math. 3 (1999); Open Problem Garden, pentagon_problem.

Problem: let G be a 3-regular graph that contains no cycle of length shorter than g.  Is it true
that for large enough g there is a homomorphism from G to the 5-cycle C_5?

The proposition states the positive answer: for some g, every 3-regular graph of girth at least g
has a homomorphism to C_5.

Encoding.  Graphs are finite and simple. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

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

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c d : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** ** Statement *)

Definition OPG_pentagon_cubic_girth_c5_homomorphism : Prop :=
  exists g : nat, forall G : sgraph,
    regular G 3 -> girth_ge G g -> homs_to G (cycle_graph 5).
