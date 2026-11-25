(** * Woodall's conjecture

Woodall, "Menger and König systems", Theory and Applications of Graphs, Lecture Notes in Mathematics
642 (1978); Open Problem Garden, woodalls_conjecture.

A directed cut of a digraph D is the set of the arcs that leave a nonempty proper subset B of V(D),
when no arc enters B.  A dijoin is a set of arcs that meets every directed cut.

Conjecture: if the smallest directed cut of D has size k, then D has k pairwise disjoint dijoins.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Digons are allowed, and so are loops, which play no role here.  Parallel arcs are
not represented, which is no restriction.  Indeed, if the arcs of a digraph with parallel arcs are
subdivided, then the minimum size of a directed cut does not change, and the arcs whose two halves
belong to a dijoin of the new digraph form a dijoin.  The digraph need not be connected: the
smallest directed cut of a disconnected digraph is empty. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** The arcs from [B] to its complement. *)
Definition outcut (D : diGraph) (B : {set D}) : {set D * D} :=
  [set p : D * D | [&& p.1 \in B, p.2 \notin B & p.1 -- p.2]].

(** [B] is the source side of a dicut: it is nonempty and proper, and no arc enters it
    (the dicut is then [outcut B]). *)
Definition dicut_side (D : diGraph) (B : {set D}) : bool :=
  [&& B != set0, B != [set: D] & outcut (~: B) == set0].

(** The arc set [F] is a dijoin: it meets all the dicuts of [D]. *)
Definition dijoin (D : diGraph) (F : {set D * D}) : bool :=
  (F \subset arcs D) && [forall B : {set D}, dicut_side B ==> ~~ [disjoint F & outcut B]].

(** ** Statement *)

Definition OPG_woodall_dicut_disjoint_dijoins : Prop :=
  forall (D : diGraph) (k : nat),
    (exists2 B : {set D}, dicut_side B & #|outcut B| = k) ->
    (forall B : {set D}, dicut_side B -> k <= #|outcut B|) ->
    exists J : 'I_k -> {set D * D},
      (forall i : 'I_k, dijoin (J i)) /\
      (forall i j : 'I_k, i != j -> [disjoint J i & J j]).
