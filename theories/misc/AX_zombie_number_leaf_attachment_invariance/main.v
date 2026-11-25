(** * Zombie number and vertices of degree 1

Bartier, Bénéteau, Bonamy, La, Narboni, "A note on deterministic zombies", arXiv:2008.03587,
Question 4.1 (2008.03587__00).

In the game of zombies and survivors on a connected graph G, the zombies choose their vertices,
then the survivor chooses a vertex.  In each round, every zombie moves to a neighbour along a
shortest path towards the survivor (the zombies choose the shortest paths), then the survivor
stays or moves to a neighbour.  The zombies win if some zombie is on the vertex of the survivor at
some point.  The zombie number z(G) is the minimum number of zombies that can win, whatever the
survivor does.

Question 4.1: for every connected graph G and every graph G' obtained from G by successively adding
vertices of degree 1, does z(G') = z(G) always hold?

The proposition states the positive answer.

Encoding.  G is nonempty, and G' is taken up to isomorphism.  The zombies win if, for some t, they
can ensure capture in at most t rounds (this is equivalent to an eventual capture, as the graph is
finite).  z(G) = k is the predicate [zombie_number G k]. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

Section CopsAndRobbers.
Variable G : sgraph.

(** The positions of [k] cops. *)
Definition cop_position (k : nat) := {ffun 'I_k -> G}.

(** Some cop is on the vertex [r] of the robber. *)
Definition captured (k : nat) (C : cop_position k) (r : G) : bool :=
  [exists i : 'I_k, C i == r].

End CopsAndRobbers.

Section ZombiesAndSurvivors.
Variable G : sgraph.

(** A move of the zombies: each one goes to a neighbour closer to [s]. *)
Definition zombie_move (k : nat) (s : G) (Z Z' : cop_position G k) : bool :=
  [forall i : 'I_k, (Z i -- Z' i) && (graph_dist (Z' i) s < graph_dist (Z i) s)].

(** The zombies can capture the survivor in at most [t] rounds. *)
Fixpoint zombies_capture (k t : nat) (Z : cop_position G k) (s : G) {struct t} : bool :=
  captured Z s ||
  (if t is t'.+1 then
     [exists Z' : cop_position G k,
        zombie_move s Z Z' &&
        (captured Z' s ||
         [forall s' : G, s -*- s' ==> zombies_capture t' Z' s'])]
   else false).

(** For some initial position, [k] zombies win in at most [t] rounds. *)
Definition zombies_win_within (k t : nat) : bool :=
  [exists Z0 : cop_position G k, [forall s0 : G, zombies_capture t Z0 s0]].

(** [k] zombies win. *)
Definition zombies_win (k : nat) : Prop := exists t : nat, zombies_win_within k t.

(** The zombie number of [G] is [k]: the minimum number of zombies that win. *)
Definition zombie_number (k : nat) : Prop :=
  zombies_win k /\ forall j : nat, j < k -> ~ zombies_win j.

End ZombiesAndSurvivors.

(** ** Definitions specific to the conjecture *)

(** The graphs obtained from [G] by successively adding vertices of degree 1, up to
    isomorphism: [add_node H [set v]] is [H] with a new vertex, adjacent to [v] only. *)
Inductive pendant_extension (G : sgraph) : sgraph -> Prop :=
| pendant_refl (G' : sgraph) : inhabited (G ≃ G') -> pendant_extension G G'
| pendant_step (H : sgraph) (v : H) (G' : sgraph) :
    pendant_extension G H -> inhabited (add_node H [set v] ≃ G') ->
    pendant_extension G G'.

(** ** Statement *)

Definition AX_zombie_number_leaf_attachment_invariance : Prop :=
  forall G G' : sgraph,
    connected [set: G] -> 0 < #|G| ->
    pendant_extension G G' ->
    forall z z' : nat, zombie_number G z -> zombie_number G' z' -> z' = z.
