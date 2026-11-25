(** * Good edge labellings and density

Araújo, Cohen, Giroire, Havet, "Good edge-labelling of graphs", LAGOS 2009; Open Problem Garden,
good_edge_labelings.

A good edge labelling of a graph is an assignment of distinct numbers to its edges such that every
cycle has at least two local maxima.  Equivalently, for all distinct vertices u and v, there is at
most one path from u to v along which the labels increase.  A graph is critical if it has no good
edge labelling, but each of its proper subgraphs has one.

Conjecture: for every c < 4, there are finitely many critical graphs with average degree less than
c.

The source also asks for the maximum edge density of a graph that has a good edge labelling.  Only
the conjecture is stated here.

Encoding.  The definition by increasing paths is used, with natural numbers as labels.  The number
c is a rational a / b, which is not a restriction.  Finitely many graphs, up to isomorphism, means
that their number of vertices is bounded.  Subgraphs are considered up to isomorphism. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The average degree of [G] is at least [a / b]. *)
Definition average_degree_ge (G : sgraph) (a b : nat) : Prop :=
  a * #|G| <= b * (\sum_(v in G) #|N(v)|).

(** ** Definitions copied from GraphLib/extremal.v *)

(** [H] is a proper subgraph of [G] (up to isomorphism). *)
Definition proper_subgraph (H G : sgraph) : Prop := subgraph H G /\ ~ subgraph G H.

(** [p] is a nonempty path from [u] to [v] whose labels are increasing. *)
Definition increasing_path (G : sgraph) (l : G -> G -> nat) (u v : G) (p : seq G) : bool :=
  [&& uniq (u :: p), path (--) u p, last u p == v,
      sorted ltn (pairmap l u p) & p != [::] ].

(** [G] has a good edge labelling: the labels are distinct and, for all vertices [u] and [v],
    there is at most one increasing path from [u] to [v]. *)
Definition good_edge_labeling (G : sgraph) : Prop :=
  exists l : G -> G -> nat,
    [/\ (forall x y : G, l x y = l y x),
        (forall x y x' y' : G,
            x -- y -> x' -- y' -> x != y -> x' != y' ->
            l x y = l x' y' -> [set x; y] == [set x'; y']) &
        (forall (u v : G) (p q : seq G),
            increasing_path l u v p -> increasing_path l u v q -> p = q) ].

(** ** Definitions specific to the conjecture *)

(** [G] is critical: it has no good edge labelling, but its proper subgraphs have one. *)
Definition gel_critical (G : sgraph) : Prop :=
  ~ good_edge_labeling G /\
  (forall H : sgraph, proper_subgraph H G -> good_edge_labeling H).

(** ** Statement *)

Definition OPG_good_edge_labeling_max_density : Prop :=
  forall a b : nat, 0 < b -> a < 4 * b ->
    exists N : nat, forall G : sgraph,
      gel_critical G -> ~ average_degree_ge G a b -> #|G| <= N.
