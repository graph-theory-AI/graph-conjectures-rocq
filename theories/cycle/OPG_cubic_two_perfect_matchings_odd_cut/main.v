(** * The intersection of two perfect matchings

Máčajová and Škoviera; Open Problem Garden, intersecting_two_perfect_matchings.

A bridge is an edge whose deletion disconnects its two ends.  A graph is cubic if all its degrees
are 3.  A perfect matching is a set M of edges such that every vertex is the end of exactly one
edge of M.  An odd edge-cut is a set of edges of odd size that consists of the edges with exactly
one end in some set of vertices.

Conjecture: every bridgeless cubic graph has two perfect matchings M_1, M_2 such that M_1 ∩ M_2
contains no odd edge-cut.

Encoding.  Graphs are the finite multigraphs of GraphTheory: parallel edges are allowed, and
loops are excluded (in a cubic graph a loop would entail a bridge).  The reference direction of
the edges plays no role.  The empty graph is excluded.  The two perfect matchings are not
required to be distinct. *)

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

(** The edges with exactly one end in [S]. *)
Definition mcut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

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

(** ** Definitions copied from GraphLib/cycle.v *)

Section EdgeSets.
Variable G : mgraph.
Implicit Types S T : {set edge G}.

(** [T] is a cut with an odd number of edges. *)
Definition odd_edge_cut T : Prop :=
  exists S : {set G}, [/\ T = mcut S, T != set0 & odd #|T|].

End EdgeSets.

(** ** Definitions specific to the conjecture *)

(** The edge set [H] contains an odd edge-cut. *)
Definition contains_odd_edge_cut (G : mgraph) (H : {set edge G}) : Prop :=
  exists T : {set edge G}, T \subset H /\ odd_edge_cut T.

(** ** Statement *)

Definition OPG_cubic_two_perfect_matchings_odd_cut : Prop :=
  forall G : mgraph,
    0 < #|G| -> loopless_cubic G /\ bridgeless G ->
    exists M1 M2 : {set edge G},
      [/\ mperfect_matching M1, mperfect_matching M2
        & ~ contains_odd_edge_cut (M1 :&: M2)].
