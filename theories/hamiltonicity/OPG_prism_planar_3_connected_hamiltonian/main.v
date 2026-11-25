(** * Prisms over 3-connected planar graphs are Hamiltonian

Kaiser, Král', Rosenfeld, Ryjáček, Voss, "Hamilton cycles in prisms", J. Graph Theory 56 (2007);
Open Problem Garden, every_prism_over_a_3_connected_planar_graph_is_hamiltonian.

The prism over G is the cartesian product G □ K_2.

Conjecture: if G is a 3-connected planar graph, then the prism over G has a Hamilton cycle.

Encoding.  Graphs are finite and simple.  A 3-connected graph has more than three vertices.
Planarity is the absence of K_5 and K_3,3 minors (Wagner's theorem). *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Products.
Variables G H : sgraph.

(** Equal in one coordinate and adjacent in the other. *)
Definition box_rel : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).

Lemma box_sym : symmetric box_rel.
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.

Lemma box_irrefl : irreflexive box_rel.
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.

(** The cartesian product of [G] and [H]. *)
Definition cartesian_product : sgraph := SGraph box_sym box_irrefl.

End Products.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Statement *)

Definition OPG_prism_planar_3_connected_hamiltonian : Prop :=
  forall G : sgraph,
    planar G -> 3.-connected G -> hamiltonian (cartesian_product G 'K_2).
