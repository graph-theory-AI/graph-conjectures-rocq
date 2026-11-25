(** * The induced Menger conjecture

Hickingbotham, Joret, "An induced A-path theorem", arXiv:2512.17232, Conjecture 6 (2512.17232__00).

An (X,Y)-path is a path with one end in X and the other in Y.  Two paths are anti-complete if they
are disjoint and no edge joins them.  N[Z] is the closed neighbourhood of Z, i.e. the set of the
vertices at distance at most 1 from Z.

Conjecture 6: for every k, every graph G and all X, Y ⊆ V(G), either G contains k pairwise
anti-complete (X,Y)-paths, or there exists Z ⊆ V(G) with |Z| <= k such that G - N[Z] has no
(X,Y)-path.

Encoding.  Graphs are finite and simple, and the paths may have only one vertex.  "G - N[Z] has no
(X,Y)-path" is: every (X,Y)-path of G meets N[Z]. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [A] and [B] are disjoint and there is no edge between them. *)
Definition anticomplete (G : sgraph) (A B : {set G}) : bool :=
  [disjoint A & B] && ~~ neighbor A B.

Section Paths.
Variable G : diGraph.
Implicit Types (p : seq G) (X Y : {set G}).

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

(** [p] is a path from a vertex of [X] to a vertex of [Y]. *)
Definition seq_path_between X Y p : bool :=
  if p is x :: q then [&& x \in X, last x q \in Y & seq_simple_path p] else false.

End Paths.

(** ** Definitions specific to the conjecture *)

(** There are [k] pairwise anti-complete paths from [X] to [Y]. *)
Definition has_k_anticomplete_paths (G : sgraph) (k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> seq_path_between X Y p) /\
    (forall p q : seq G, p \in paths -> q \in paths -> p != q ->
       anticomplete [set:: p] [set:: q]).

(** ** Statement *)

Definition AX_anticomplete_xy_paths_erdos_posa_optimal : Prop :=
  forall (k : nat) (G : sgraph) (X Y : {set G}),
    has_k_anticomplete_paths k X Y \/
    exists Z : {set G},
      #|Z| <= k /\
      forall p : seq G, seq_path_between X Y p -> ~ [disjoint [set:: p] & NS[Z]].
