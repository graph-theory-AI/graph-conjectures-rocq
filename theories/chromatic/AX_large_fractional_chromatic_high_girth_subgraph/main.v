(** * Subgraphs of large girth and large fractional chromatic number

Mohar, Wu, "Triangle-free subgraphs with large fractional chromatic number", arXiv:1808.01605,
Conjecture 4 (1808.01605__00).

The fractional chromatic number χ_f(G) is the minimum of Σ_I y_I over the weightings y >= 0 of the
independent sets I of G such that Σ_{I ∋ v} y_I >= 1 for every vertex v.

Conjecture 4: for all real x >= 1 and integer g >= 3, there is a positive number k(x,g) such that
every graph G with χ_f(G) >= k(x,g) contains a subgraph H of girth at least g with χ_f(H) >= x.

Encoding.  Graphs are finite and simple, and forests have infinite girth.  The numbers x and k(x,g)
are integers, without loss of generality (they can be rounded up).  "χ_f(G) >= k" means that, for
all b >= 1, at least kb colours are needed to give b colours to each vertex, with disjoint sets on
adjacent vertices.  This is equivalent, since the linear program has a rational optimal
solution. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** The girth of [G] is at least [g] (true if [G] is a forest). *)
Definition girth_ge (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, seq_cycle (--) c -> g <= size c.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional chromatic number of [G] is at least the integer [k]. *)
Definition fractional_chromatic_ge (G : sgraph) (k : nat) : Prop :=
  forall a b : nat, 0 < b -> weighted_colorable (fun _ : G => b) a -> k * b <= a.

(** ** Statement *)

Definition AX_large_fractional_chromatic_high_girth_subgraph : Prop :=
  forall x g : nat, 1 <= x -> 3 <= g ->
    exists k : nat, 0 < k /\
      forall G : sgraph, fractional_chromatic_ge G k ->
        exists H : sgraph, [/\ subgraph H G, girth_ge H g & fractional_chromatic_ge H x].
