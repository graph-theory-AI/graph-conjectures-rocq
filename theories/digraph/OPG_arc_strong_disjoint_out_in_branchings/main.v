(** * Arc-disjoint out-branching and in-branching

Thomassen, "Configurations in graphs of large minimum degree, connectivity, or chromatic
number", Annals of the New York Academy of Sciences 555 (1989);
Open Problem Garden, arc_disjoint_out_branching_and_in_branching.

A digraph D is k-arc-strong if at least k arcs leave every nonempty proper subset of V(D), that
is, if D remains strongly connected when fewer than k arcs are deleted.  An out-branching
rooted at u is a spanning oriented tree of D in which u has in-degree 0 and every other vertex
has in-degree 1.  An in-branching rooted at v is a spanning oriented tree of D in which v has
out-degree 0 and every other vertex has out-degree 1.

Conjecture: there is an integer k such that, for every k-arc-strong digraph D and all vertices
u and v of D, D contains an out-branching rooted at u and an in-branching rooted at v that are
arc-disjoint.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a
boolean relation [--].  Digons are allowed, and so are loops, which play no role here.  Parallel
arcs are not represented.  The vertices u and v may be equal.  A digraph with a single vertex is
k-arc-strong for every k, and it trivially satisfies the conclusion, with branchings that have
no arc. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** In-degree. *)
Definition indeg (D : diGraph) (v : D) : nat := #|[set u | u -- v]|.

(** Out-degree. *)
Definition outdeg (D : diGraph) (v : D) : nat := #|N(v)|.

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The digraph on [T] with arc set [A]. *)
Definition digraph_of_arcs (T : finType) (A : {set T * T}) : diGraph :=
  DiGraph (fun x y : T => (x, y) \in A).

(** The arcs from [B] to its complement. *)
Definition outcut (D : diGraph) (B : {set D}) : {set D * D} :=
  [set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 -- p.2]].

(** [D] is [k]-arc-strong: at least [k] arcs leave each nonempty proper set of vertices (always
    true if [D] has at most one vertex). *)
Definition arc_strong (D : diGraph) (k : nat) : bool :=
  [forall B : {set D}, ((B != set0) && (B != [set: D])) ==> (k <= #|outcut B|)].

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** [F] is the arc set of a spanning out-branching rooted at [r]. *)
Definition out_branching (D : diGraph) (F : {set D * D}) (r : D) : bool :=
  let B := digraph_of_arcs F in
  [&& F \subset arcs D, @indeg B r == 0,
      [forall v : D, (v != r) ==> (@indeg B v == 1)] & acyclic B].

(** [F] is the arc set of a spanning in-branching rooted at [r]. *)
Definition in_branching (D : diGraph) (F : {set D * D}) (r : D) : bool :=
  let B := digraph_of_arcs F in
  [&& F \subset arcs D, @outdeg B r == 0,
      [forall v : D, (v != r) ==> (@outdeg B v == 1)] & acyclic B].

(** ** Statement *)

Definition OPG_arc_strong_disjoint_out_in_branchings : Prop :=
  exists k : nat, forall (D : diGraph) (u v : D), arc_strong D k ->
    exists F F' : {set D * D}, [/\ out_branching F u, in_branching F' v & [disjoint F & F']].
