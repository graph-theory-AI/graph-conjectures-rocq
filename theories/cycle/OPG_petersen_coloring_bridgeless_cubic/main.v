(** * The Petersen colouring conjecture

Jaeger; Open Problem Garden, petersen_coloring_conjecture.

A bridge is an edge whose deletion disconnects its two ends.  A graph is cubic if all its degrees
are 3.  Two edges are adjacent if they are distinct and have a common end.

Conjecture: if G is a bridgeless cubic graph, then the edges of G can be coloured by the edges of
the Petersen graph so that any three mutually adjacent edges of G are mapped to three mutually
adjacent edges of the Petersen graph.

Encoding.  Graphs are the finite multigraphs of GraphTheory: parallel edges are allowed, and
loops are excluded (in a cubic graph a loop would entail a bridge).  The reference direction of
the edges plays no role.  The empty graph is excluded.  The Petersen graph is the Kneser graph of
the 2-element subsets of a 5-element set.  Its edges are represented by ordered pairs of adjacent
vertices: an edge has two representatives, which are identified by comparing their sets of
ends. *)

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

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

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

(** ** Definitions specific to the conjecture *)

(** The vertices of the Petersen graph: the 2-element subsets of a 5-element set. *)
Definition petersenV : finType := {x : {set 'I_5} | #|x| == 2}.

(** Disjoint subsets are adjacent. *)
Definition petersen_adj (x y : petersenV) : bool := [disjoint val x & val y].

(** The edges of the Petersen graph, as ordered pairs of adjacent vertices. *)
Definition petersen_edge : finType := {p : petersenV * petersenV | petersen_adj p.1 p.2}.

(** The set of ends of the edge [q]. *)
Definition petersen_ends (q : petersen_edge) : {set petersenV} := [set (val q).1; (val q).2].

(** [q] and [r] are distinct edges with a common end. *)
Definition petersen_edge_adj (q r : petersen_edge) : bool :=
  (petersen_ends q != petersen_ends r) && (petersen_ends q :&: petersen_ends r != set0).

(** [a], [b] and [c] are pairwise related by [r]. *)
Definition mutually_adjacent (T : Type) (r : rel T) (a b c : T) : bool :=
  [&& r a b, r b c & r a c].

(** ** Statement *)

Definition OPG_petersen_coloring_bridgeless_cubic : Prop :=
  forall G : mgraph,
    0 < #|G| -> loopless_cubic G /\ bridgeless G ->
    exists f : edge G -> petersen_edge,
      forall e1 e2 e3 : edge G,
        mutually_adjacent (@mline_rel G) e1 e2 e3 ->
        mutually_adjacent petersen_edge_adj (f e1) (f e2) (f e3).
