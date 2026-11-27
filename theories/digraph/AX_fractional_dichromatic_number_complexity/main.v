(** * Complexity of the fractional dichromatic number

Hochstättler, Schröder, Steiner, "On the complexity of digraph colourings and vertex
arboricity", DMTCS 22:1 (2020), arXiv:1812.02420, Problem 3.21 (1812.02420__02).

A set of vertices of a digraph D is acyclic if it induces a digraph without directed cycle
(two opposite arcs form a directed cycle of length two, a digon).  The dichromatic number
χ(D) is the minimum number of acyclic sets that partition V(D).  The fractional dichromatic
number χ_f(D) is the minimum of Σ_A x_A over the weightings x >= 0 of the acyclic sets such
that Σ_{A ∋ v} x_A >= 1 for every vertex v.

Problem 3.21: for a fixed real p >= 1, decide whether χ_f(D) <= p.  It is polynomial for
p = 1 and NP-complete for every p > 1 with p <> 2.  The authors believe that the open case
p = 2 is NP-complete too.

What is stated here is only a proxy, as complexity classes are not formalized: the reduction
that gives this NP-completeness.  For a digraph D, let R(D) consist of two copies of D where
each vertex is joined to its copy by a digon.  Then χ_f(R(D)) <= 2 if and only if χ(D) <= 2,
and R(D) has 2|V| vertices and 2|A| + 2|V| arcs.

The proxy is stronger than the conjecture, which follows from it and from three facts that
remain outside the statement: deciding χ(D) <= 2 is NP-hard (Bokal, Fijavž, Juvan, Kayll,
Mohar, J. Graph Theory 46, 2004), deciding χ_f(D) <= 2 is in NP (Observation 3.15 of the
source), and R(D) is computable in polynomial time (its arcs are given by an explicit boolean
formula, see [two_layer]).

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Digons are allowed, as in the source.  Parallel arcs are not
represented, which changes neither the acyclic sets nor the hardness.  Loops are allowed,
which is more general, and R(D) is loopless when D is.  "χ_f(D) <= p" is expressed by the
existence of a feasible x of total weight at most p.  This is equivalent, as the minimum of
this linear program is attained whenever it is feasible.  The weights are in an arbitrary
ordered field (rational or real numbers for instance). *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot order ssralg ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** ** Definitions copied from GraphLib/fractional.v *)

(** The fractional dichromatic number of [D] is at most [p]: nonnegative weights on the
    sets inducing an acyclic digraph, of total at most [p], cover each vertex with weight
    at least 1.  Weights are taken in an ordered field [R]. *)
Definition fractional_dicolorable (R : realFieldType) (D : diGraph) (p : R) : Prop :=
  (exists x : {set D} -> R,
    [/\ forall A : {set D}, 0 <= x A,
        forall v : D, 1 <= \sum_(A : {set D} | acyclic (induced A) && (v \in A)) x A
      & \sum_(A : {set D} | acyclic (induced A)) x A <= p])%R.

(** ** Definitions specific to the conjecture *)

(** R(D): the vertices are the pairs (v,i) where i is a boolean, and there is an arc from
    (u,i) to (v,j) if i = j and u -- v is an arc of D, or if u = v and i <> j. *)
Definition two_layer (D : diGraph) : diGraph :=
  DiGraph [rel a b : D * bool |
    ((a.2 == b.2) && (a.1 -- b.1)) || ((a.1 == b.1) && (a.2 != b.2))].

(** ** Statement *)

(** The reduction that gives NP-completeness, as believed by the authors. *)
Definition proxy_AX_fractional_dichromatic_number_complexity : Prop :=
  forall (R : realFieldType) (D : diGraph),
    [/\ fractional_dicolorable (two_layer D) (2%R : R) <-> dicolorable D 2,
        #|two_layer D| = 2 * #|D|
      & num_edges (two_layer D) = 2 * num_edges D + 2 * #|D|].
