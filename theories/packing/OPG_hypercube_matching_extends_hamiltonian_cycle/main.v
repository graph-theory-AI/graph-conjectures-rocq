(** * Matchings extend to Hamiltonian cycles in hypercubes

Ruskey, Savage, SIAM Journal on Discrete Mathematics 6 (1993); Open Problem Garden,
matchings_extends_to_hamilton_cycles_in_hypercubes.

The hypercube of dimension d is the graph on {0,1}^d where two vertices are adjacent if they differ
in exactly one coordinate.

Question: does every matching of a hypercube extend to a Hamiltonian cycle?

The proposition states the positive answer.

Encoding.  The dimension is at least 2, as the hypercubes of dimensions 0 and 1 have no Hamiltonian
cycle.  A matching is a set of pairwise disjoint edges (as sets of two vertices), possibly empty. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

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

Section Hypercube.
Variable d : nat.

(** Tuples that differ at exactly one position. *)
Definition hypercube_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.

Lemma hypercube_sym : symmetric hypercube_rel.
Proof.
move=> x y; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth y i] = [set i : 'I_d | tnth y i != tnth x i] by [].
by apply/setP => i; rewrite !inE eq_sym.
Qed.

Lemma hypercube_irrefl : irreflexive hypercube_rel.
Proof.
move=> x; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth x i] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE eqxx.
Qed.

(** The hypercube of dimension [d]. *)
Definition hypercube : sgraph := SGraph hypercube_sym hypercube_irrefl.

End Hypercube.

(** ** Definitions copied from GraphLib/hamiltonicity.v *)

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** ** Statement *)

Definition OPG_hypercube_matching_extends_hamiltonian_cycle : Prop :=
  forall (d : nat) (M : {set {set hypercube d}}),
    2 <= d -> matching M ->
    exists c : seq (hypercube d),
      hamiltonian_cycle (hypercube d) c /\ M \subset seq_cycle_edge_set c.
