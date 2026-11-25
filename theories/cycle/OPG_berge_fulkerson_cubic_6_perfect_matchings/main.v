(** * The Berge-Fulkerson conjecture

Berge and Fulkerson: Fulkerson, "Blocking and anti-blocking pairs of polyhedra", Math.
Programming 1 (1971); Open Problem Garden, the_berge_fulkerson_conjecture.

A bridge is an edge whose deletion disconnects its two ends.  A graph is cubic if all its degrees
are 3.  A perfect matching is a set M of edges such that every vertex is the end of exactly one
edge of M.

Conjecture: every bridgeless cubic graph G has 6 perfect matchings M_1, ..., M_6, not necessarily
distinct, such that every edge of G is in exactly two of them.

Encoding.  Graphs are the finite multigraphs of GraphTheory: parallel edges are allowed, and
loops are excluded (in a cubic graph a loop would entail a bridge).  The reference direction of
the edges plays no role.  The empty graph is excluded.  The matchings form a list of length 6,
and the matchings that contain an edge are counted with their multiplicity in this list. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Every vertex is incident to three edges (a loop is counted once). *)
Definition mcubic (G : mgraph) : Prop := mregular G 3.

(** [G] is cubic and has no loop. *)
Definition loopless_cubic (G : mgraph) : Prop := mloopless G /\ mcubic G.

(** The degree of [v] in the edge set [H] (a loop is counted twice). *)
Definition mdeg_in (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|[set e in H | source e == v]| + #|[set e in H | target e == v]|.

(** The list of edges [w] is a walk from [x] to [y]; the edges are used in either direction. *)
Fixpoint uwalk (G : mgraph) (x y : G) (w : seq (edge G)) {struct w} : bool :=
  match w with
  | [::] => x == y
  | e :: w' =>
      ((source e == x) && uwalk (target e) y w') ||
      ((target e == x) && uwalk (source e) y w')
  end.

(** [e] is a bridge: every walk between its ends uses it. *)
Definition mbridge (G : mgraph) (e : edge G) : Prop :=
  forall w : seq (edge G), uwalk (source e) (target e) w -> e \in w.

(** [G] has no bridge. *)
Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ mbridge e.

(** ** Definitions copied from GraphLib/packing.v *)

(** [M] is a perfect matching of the multigraph [G] (without loops). *)
Definition mperfect_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, mdeg_in M v = 1.

(** [L] is a list of [k] perfect matchings such that each edge is in exactly two of them. *)
Definition matching_double_cover (G : mgraph) (k : nat)
    (L : seq {set edge G}) : Prop :=
  [/\ size L = k,
      (forall M, M \in L -> mperfect_matching M)
    & forall e : edge G, count (fun M : {set edge G} => e \in M) L = 2].

(** ** Statement *)

Definition OPG_berge_fulkerson_cubic_6_perfect_matchings : Prop :=
  forall G : mgraph,
    0 < #|G| -> loopless_cubic G /\ bridgeless G ->
    exists L : seq {set edge G}, matching_double_cover 6 L.
