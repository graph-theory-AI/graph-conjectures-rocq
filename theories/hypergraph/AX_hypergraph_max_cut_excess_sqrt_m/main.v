(** * Excess of the maximum r-cuts of hypergraphs

Conlon, Fox, Kwan, Sudakov, "Hypergraph cuts above the average", arXiv:1803.08462, Θ(√m) excess
conjecture (1803.08462__00).

An r-cut of a hypergraph H is a partition of its vertex set into r parts, some of which may be
empty.  Its size is the number of edges that meet all parts.  If H is k-uniform with m edges, the
expected size of a uniformly random r-cut is S(k,r) r! m / r^k, where S(k,r) is the Stirling number
of the second kind (number of partitions of a set with k elements into r parts).  The excess of an
r-cut is the difference between its size and this number.

Conjecture: for all fixed r and k such that 2 <= r <= k, the minimum, over all k-uniform
hypergraphs with m edges, of the maximum excess of an r-cut is Θ(√m).

Encoding.  The excess is multiplied by the constant r^k so as to be an integer, and
"excess = Θ(√m)" is written "excess^2 = Θ(m)".  The subtraction in nat is not truncated, as the
maximum size of an r-cut is at least the expected size. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [P n] holds for every sufficiently large [n]. *)
Definition eventually (P : nat -> Prop) : Prop :=
  exists N : nat, forall n : nat, N <= n -> P n.

(** [f = O(g)]. *)
Definition big_O_nat (f g : nat -> nat) : Prop :=
  exists C : nat, 0 < C /\ eventually (fun n => f n <= C * g n).

(** [f = Theta(g)]. *)
Definition big_Theta_nat (f g : nat -> nat) : Prop :=
  big_O_nat f g /\ big_O_nat g f.

(** The Stirling numbers of the second kind: the number of partitions of a set with [k] elements
    into [r] parts. *)
Fixpoint stirling2 (k r : nat) : nat :=
  match k, r with
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _.+1, 0 => 0
  | k'.+1, r'.+1 => r'.+1 * stirling2 k' r'.+1 + stirling2 k' r'
  end.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** ** Definitions specific to the conjecture *)

(** The edge [e] meets all the parts of the [r]-cut [col]. *)
Definition meets_all_parts (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [forall i : 'I_r, [exists v in e, col v == i]].

(** The size of the [r]-cut [col]. *)
Definition cut_size (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | meets_all_parts col e]|.

(** The maximum size of an [r]-cut is [c]. *)
Definition max_cut (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    cut_size E col = c /\ forall col' : T -> 'I_r, cut_size E col' <= c.

(** The maximum excess of an [r]-cut of the [k]-uniform hypergraph [E] is [x / r ^ k]. *)
Definition scaled_excess (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat, max_cut E r c /\ x = r ^ k * c - stirling2 k r * r`! * #|E|.

(** The minimum over all [k]-uniform hypergraphs with [m] edges of the maximum excess of an
    [r]-cut is [x / r ^ k]. *)
Definition min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ hg_uniform E k, #|E| = m, scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T'}}) (y : nat),
          hg_uniform E' k -> #|E'| = m -> scaled_excess E' r k y -> x <= y].

(** ** Statement *)

Definition AX_hypergraph_max_cut_excess_sqrt_m : Prop :=
  forall r k : nat, 2 <= r -> r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => excess m ^ 2) (fun m => m).
