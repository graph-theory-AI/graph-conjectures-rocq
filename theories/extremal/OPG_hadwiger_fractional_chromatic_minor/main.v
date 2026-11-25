(** * Fractional Hadwiger conjecture

Reed, Seymour, "Fractional colouring and Hadwiger's conjecture", J. Combin. Theory Ser. B 74
(1998), for (a); Harvey, Wood, "Parameters tied to treewidth", arXiv:1312.3401, for (b) and (c);
Pedersen, PhD thesis, University of Southern Denmark, for (c); Open Problem Garden,
fractional_hadwiger.

The Hadwiger number had(G) is the largest h such that the complete graph K_h is a minor of G.  Two
sets of vertices touch if they intersect or if there is an edge between them.  The fractional
Hadwiger number had_f(G) is the maximum total weight of a family of nonempty connected sets of
vertices that pairwise touch, with nonnegative weights, such that the sets containing any given
vertex have total weight at most 1.  The fractional chromatic number χ_f(G) is the minimum of a/b
such that each vertex can be given b colours among a, adjacent vertices having disjoint sets of
colours.

Conjecture: for every graph G, (a) χ_f(G) <= had(G), (b) χ(G) <= had_f(G) and
(c) χ_f(G) <= had_f(G).

Encoding.  The proposition is the conjunction of (a), (b) and (c).  Graphs are finite, simple and
nonempty.  The numbers χ_f, had and had_f are given by relations; they exist for all nonempty
graphs, and they are rational.  In the definition of had_f, distinct members of the family are
joined by an edge, instead of touching; this is equivalent, as two connected sets that intersect
are joined by an edge unless they are the same set with one vertex, which can be taken once, with
the sum of the weights. *)

From GraphTheory Require Import preliminaries digraph sgraph coloring minor.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** There is a weighted colouring with [k] colours: each vertex [v] receives a set of [p v]
    colours, and adjacent vertices receive disjoint sets. *)
Definition weighted_colorable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

(** The fractional chromatic number of [G] is [r]. *)
Definition fractional_chromatic_number (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\
     weighted_colorable (fun _ : G => b) a /\ r = (a%:Q / b%:Q)%R) /\
  (forall a b : nat, (0 < b)%N ->
     weighted_colorable (fun _ : G => b) a -> (r <= a%:Q / b%:Q)%R).

(** ** Definitions copied from GraphLib/minor.v *)

(** The Hadwiger number of [G] is [h]. *)
Definition hadwiger_number (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\ (forall h', minor G 'K_h' -> (h' <= h)%N).

(** [B] and [w] are a fractional clique minor of [G] of value [r]: the branch sets [B i] are
    nonempty and connected, there is an edge between any two of them (they may overlap), and the
    sum of the weights of those containing a given vertex is at most 1. *)
Definition fractional_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, (0 <= w i)%R),
      (forall i, B i != set0 /\ connected (B i)),
      (forall i j, i != j -> neighbor (B i) (B j)),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & (r = \sum_i w i)%R].

(** The fractional Hadwiger number of [G] is [r]. *)
Definition fractional_hadwiger_number (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), fractional_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     fractional_clique_minor B w r' -> (r' <= r)%R).

(** ** Statement *)

Definition OPG_hadwiger_fractional_chromatic_minor : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    0 < #|G| ->
    fractional_chromatic_number G xf -> hadwiger_number G h -> fractional_hadwiger_number G hf ->
    [/\ xf <= h%:Q, (χ([set: G]))%:Q <= hf & xf <= hf]%R.
