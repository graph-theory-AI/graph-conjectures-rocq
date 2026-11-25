(** * Mapping planar graphs to odd cycles

Jaeger, "On circular flows in graphs", Finite and Infinite Sets, Colloq. Math. Soc. János Bolyai 37
(1981); Open Problem Garden, mapping_planar_graphs_to_odd_cycles.

Conjecture: every planar graph of girth at least 4k has a homomorphism to the odd cycle C_{2k+1}.

Encoding.  Graphs are finite and simple.  Planarity is the absence of K_5 and K_3,3 minors (Wagner's
theorem).  The girth of a forest is infinite.  It is assumed that k >= 1, which is implicit in the
source. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
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

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** ** Statement *)

Definition OPG_planar_girth_4k_homomorphism_odd_cycle : Prop :=
  forall (G : sgraph) (k : nat),
    0 < k -> planar G -> girth_ge G (4 * k) -> homs_to G (cycle_graph (2 * k + 1)).
