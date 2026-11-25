(** * Gyárfás-Sumner conjecture for tournaments

Aboulker, Aubian, Charbit, Lopes, "Clique number of tournaments", 2023, arXiv:2310.04265,
Conjecture 4.3 (2310.04265__05).

The dichromatic number χ(D) of a digraph D is the minimum number of sets in a partition of V(D) into
sets inducing acyclic subdigraphs.  For a linear order < on V(D), the backedge graph D^< is the
graph on V(D) with an edge uv whenever u < v and vu is an arc.  The clique number ω(D) is the
minimum of ω(D^<) over the linear orders <.  A tournament H is χ-binding if the tournaments that do
not contain H as a subtournament have their dichromatic number bounded by a function of their
clique number.

Conjecture: a tournament H is χ-binding if and only if it has a backedge graph that is a forest.

Encoding.  Digraphs are those of GraphTheory ([diGraph]: a finite type of vertices with a boolean
relation [--]).  A linear order on the vertices is given by a permutation, composed with the
canonical enumeration. *)

From GraphTheory Require Import sgraph coloring digraph.
From mathcomp Require Import boot perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number, i.e., the least [k] such that the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dichromatic_number (D : diGraph) : nat :=
  \big[minn/#|D|]_(k < #|D|.+1 |
     [exists col : {ffun D -> 'I_k}, [forall i : 'I_k, acyclic (induced [set v | col v == i])]])
     (k : nat).

(** [u] is before [v] in the order given by [p]. *)
Definition perm_lt (V : finType) (p : {perm V}) (u v : V) : bool :=
  enum_rank (p u) < enum_rank (p v).

Lemma perm_lt_irrefl (V : finType) (p : {perm V}) : irreflexive (perm_lt p).
Proof. by move=> u; rewrite /perm_lt ltnn. Qed.

(** There is an arc between [u] and [v] that goes backward in the order given by [p]. *)
Definition backedge_rel (D : diGraph) (p : {perm D}) : rel D :=
  [rel u v | perm_lt p u v && (v -- u) || perm_lt p v u && (u -- v)].

Lemma backedge_sym (D : diGraph) (p : {perm D}) : symmetric (backedge_rel p).
Proof. by move=> u v; rewrite /backedge_rel /= orbC. Qed.

Lemma backedge_irrefl (D : diGraph) (p : {perm D}) : irreflexive (backedge_rel p).
Proof. by move=> u; rewrite /backedge_rel /= perm_lt_irrefl. Qed.

(** The backedge graph of [D] in the order given by [p]. *)
Definition backedge_graph (D : diGraph) (p : {perm D}) : sgraph :=
  SGraph (backedge_sym p) (backedge_irrefl p).

(** The clique number of the digraph [D]: the minimum clique number of a backedge graph. *)
Definition diclique_number (D : diGraph) : nat :=
  ω([set: backedge_graph [arg min_(p < (1%g : {perm D})) ω([set: backedge_graph p])]]).

(** The dichromatic number is bounded by a function of the clique number in the class [C]. *)
Definition dichi_bounded (C : diGraph -> Prop) : Prop :=
  exists f : nat -> nat, forall D : diGraph, C D ->
    (dichromatic_number D <= f (diclique_number D))%N.

(** ** Definitions specific to the conjecture *)

(** [H] is χ-binding. *)
Definition dichi_binding (H : diGraph) : Prop :=
  dichi_bounded (fun T => tournament T /\ ~ inhabited (H ⇀ T)).

(** ** Statement *)

Definition AX_tournament_clique_number_gyarfas_sumner_backedge : Prop :=
  forall H : diGraph, tournament H ->
    dichi_binding H <-> exists p : {perm H}, is_forest [set: backedge_graph p].
