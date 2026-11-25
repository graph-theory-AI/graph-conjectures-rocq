(** * Meyniel's conjecture for k-uniform hypergraphs

Erde, Kang, Lehner, Mohar, Schmid, "Catching a robber on a random k-uniform hypergraph",
arXiv:2307.15512, Conjecture 1.4 (2307.15512__00).

In the game of cops and robber on a hypergraph H, the cops choose vertices, then the robber chooses
a vertex.  The two sides move alternately, the cops first: each piece stays at its vertex or moves
to a vertex that is in a common edge with it.  The cops win if one of them reaches the vertex of
the robber.  The cop number c(H) is the minimum number of cops that have a winning strategy.

Conjecture: c(H) = O(√(n/k)) for every connected k-uniform hypergraph H on n vertices.

Encoding.  The game on H is the game on the graph, called the 2-section of H, where two vertices
are adjacent if they are in a common edge of H.  Winning means capturing the robber in at most t
rounds, for some t that depends only on H and the number of cops.  The bound is c(H) <= C √(n/k)
for an absolute constant C, independent of n, k and H, with c(H)^2 k <= C^2 n instead of the square
root.  1 <= k <= n is assumed, so as to exclude the hypergraph with one vertex and no edge when
k >= 2 (it is k-uniform for every k). *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

Section CopsAndRobbers.
Variable G : sgraph.

(** The positions of [k] cops. *)
Definition cop_position (k : nat) := {ffun 'I_k -> G}.

(** Some cop is on the vertex [r] of the robber. *)
Definition captured (k : nat) (C : cop_position k) (r : G) : bool :=
  [exists i : 'I_k, C i == r].

(** A move of the cops: each one stays or goes to a neighbour. *)
Definition cop_move (k : nat) (C C' : cop_position k) : bool :=
  [forall i : 'I_k, C i -*- C' i].

(** The cops, who play first, capture the robber in at most [t] rounds. *)
Fixpoint cops_capture (k t : nat) (C : cop_position k) (r : G) {struct t} : bool :=
  captured C r ||
  (if t is t'.+1 then
     [exists C' : cop_position k,
        cop_move C C' &&
        (captured C' r ||
         [forall r' : G, r -*- r' ==> cops_capture t' C' r'])]
   else false).

(** For some initial position, [k] cops win in at most [t] rounds. *)
Definition cops_win_within (k t : nat) : bool :=
  [exists C0 : cop_position k, [forall r0 : G, cops_capture t C0 r0]].

(** [k] cops win. *)
Definition cops_win (k : nat) : Prop := exists t : nat, cops_win_within k t.

End CopsAndRobbers.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}) (v : T).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

(** [u] and [v] are in a common edge. *)
Definition hg_adjacent E : rel T := fun u v => [exists e in E, (u \in e) && (v \in e)].

(** Any two vertices are joined by a walk (isolated vertices matter). *)
Definition hg_connected E : Prop := forall u v : T, connect (hg_adjacent E) u v.

(** The 2-section of [E]: two vertices are adjacent if they are in a common edge. *)
Definition two_section E : sgraph := sgraph_of_rel (hg_adjacent E).

End Hypergraph.

(** ** Statement *)

Definition AX_meyniel_cop_number_k_uniform_hypergraph : Prop :=
  exists C : nat,
    forall (T : finType) (E : {set {set T}}) (k : nat),
      0 < k -> k <= #|T| ->
      hg_uniform E k -> hg_connected E ->
      exists c : nat, cops_win (two_section E) c /\ c ^ 2 * k <= C ^ 2 * #|T|.
