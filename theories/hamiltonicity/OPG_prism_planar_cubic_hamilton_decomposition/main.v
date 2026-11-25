(** * Hamilton decomposition of prisms over 3-connected cubic planar graphs

Alspach, Rosenfeld, "On Hamilton decompositions of prisms over simple 3-polytopes", Graphs Combin. 2
(1986); Open Problem Garden,
decomposing_the_prism_of_a_3_connected_cubic_planar_graphs_in_hamilton_cycles.

The prism over G is the cartesian product G □ K_2.

Conjecture: every prism over a 3-connected cubic planar graph can be decomposed into two Hamilton
cycles.

Encoding.  Graphs are finite and simple.  A 3-connected graph has more than three vertices.
Planarity is the absence of K_5 and K_3,3 minors (Wagner's theorem). *)

From GraphTheory Require Import digraph sgraph connectivity minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

Section Sequences.
Variable T : finType.
Implicit Types c : seq T.

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

(** The set of the pairs of consecutive elements of the cyclic sequence [c]: the edge set of the
    cycle [c]. *)
Definition seq_cycle_edge_set c : {set {set T}} := [set e in seq_cycle_edge_list c].

End Sequences.

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

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** [G] can be decomposed into two Hamilton cycles: their edge sets partition the set of edges. *)
Definition hamilton_decomposition_into_two (G : sgraph) : Prop :=
  exists c1 c2 : seq G,
    [/\ hamiltonian_cycle G c1, hamiltonian_cycle G c2,
        [disjoint seq_cycle_edge_set c1 & seq_cycle_edge_set c2]
      & seq_cycle_edge_set c1 :|: seq_cycle_edge_set c2 = E(G)].

(** ** Statement *)

Definition OPG_prism_planar_cubic_hamilton_decomposition : Prop :=
  forall G : sgraph,
    planar G -> 3.-connected G -> regular G 3 ->
    hamilton_decomposition_into_two (cartesian_product G 'K_2).
