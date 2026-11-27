(** * Feedback arc sets of (r-1)-free digraphs with r > 2n/3

Fox, Himwich, Mani, "Extremal results on feedback arc sets in digraphs", 2022, arXiv:2204.01938,
introduction (2204.01938__00).

A digraph is r-free if it contains no directed cycle of length at most r.  It is at most one edge
away from being acyclic if it has a feedback arc set (a set of arcs whose deletion leaves an acyclic
digraph) of size at most 1.

Conjecture: all (r-1)-free digraphs on n vertices with r > 2n/3 are at most one edge away from
being acyclic.

This is Conjecture 5.6 of the paper, as reported in the record.  The introduction states it for
r-free digraphs, which is weaker.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  The assumptions exclude loops and digons, which are directed cycles of length 1 and
2.  The condition r > 2n/3 is written 2n < 3r, and (r-1)-free is written: every directed cycle
has length at least r. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** Deletion of the arcs of [F]. *)
Definition del_arcs (D : diGraph) (F : {set D * D}) : diGraph :=
  DiGraph (fun u v : D => (u -- v) && ((u, v) \notin F)).

(** The vertices [c] form a directed cycle, of length [size c] (a loop or a digon is one). *)
Definition dicycle (D : diGraph) (c : seq D) : bool := ~~ nilp c && ucycleb (--) c.

(** The directed girth of [D] is larger than [r]. *)
Definition digirth_gt (D : diGraph) (r : nat) : Prop :=
  forall c : seq D, dicycle c -> (r < size c)%N.

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The minimum size of a set of arcs that meets all directed cycles. *)
Definition feedback_arc_number (D : diGraph) : nat :=
  #|[arg min_(F < [set: D * D] | acyclic (del_arcs F)) #|F|]|.

(** ** Statement *)

Definition AX_r_free_digraphs_near_acyclic : Prop :=
  forall (r : nat) (D : diGraph),
    2 * #|D| < 3 * r -> digirth_gt D r.-1 -> feedback_arc_number D <= 1.
