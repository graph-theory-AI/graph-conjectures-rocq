(** * A gold-grabbing game

Rosenfeld; Open Problem Garden, a_gold_grabbing_game; for the bound on trees, P. Micek and B.
Walczak, "A graph-grabbing game", Combin. Probab. Comput. 20 (2011).

Fix a tree T and, for every vertex v, a non-negative integer g(v), the amount of gold at v.  Two
players alternate turns.  On each turn, a player chooses a leaf v of the tree, takes the gold at
this vertex, and then deletes v.  The game ends when the tree is empty, and the winner is the
player who has accumulated the most gold.

Problem: find optimal strategies for the players.  In particular, if T is a path with an even
number of vertices, the first player can take all the vertices of one parity; hence she gets at
least as much gold as the second one, and wins if the two parities have different totals.

Statement: optimal strategies exist for every tree T.  If T has an even number of vertices, they
give at least half of the gold to the first player.  If moreover T is a path, they give her at
least the gold of each of the two parity classes.

Encoding.  Proxy (weaker): the problem asks for a description of optimal strategies, which is not
a definite statement; the proposition only says that they exist and bounds the gold of the first
player, for paths as in the source and for trees as conjectured by Micek and Walczak.  The
strategies are given by functions val and σ: when S is the set of remaining vertices, val(S) is
the maximum amount of gold that the player to move can ensure, and the move σ(S) ensures it.
After a move v, the opponent gets val(S - v), and the player gets the rest of the gold of S - v.
A vertex of S can be taken if it has at most one neighbour in S, hence also the last vertex.  A
path is a tree with maximum degree at most 2; its parity classes are the sets A such that A and
its complement are stable. *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** The vertex [v] of [S] can be taken. *)
Definition is_leaf (G : sgraph) (S : {set G}) (v : G) : bool :=
  (v \in S) && (#|N(v) :&: S| <= 1).

(** [val] gives the value of the game for the player to move, and [sigma] an optimal move. *)
Definition leaf_game_solution (G : sgraph) (g : G -> nat)
  (val : {set G} -> nat) (sigma : {set G} -> G) : Prop :=
  forall S : {set G},
    (~ (exists v : G, is_leaf S v) -> val S = 0) /\
    ((exists v : G, is_leaf S v) ->
       [/\ is_leaf S (sigma S),
           val S = g (sigma S) + \sum_(u in S :\ sigma S) g u - val (S :\ sigma S) &
           (forall w : G, is_leaf S w ->
              g w + \sum_(u in S :\ w) g u - val (S :\ w) <= val S)]).

(** ** Statement *)

Definition proxy_OPG_gold_grabbing_tree_game_strategy : Prop :=
  forall (G : sgraph) (g : G -> nat),
    0 < #|G| ->
    is_tree [set: G] ->
    exists (val : {set G} -> nat) (sigma : {set G} -> G),
      [/\ leaf_game_solution g val sigma,
          ~~ odd #|G| -> \sum_(v : G) g v <= 2 * val [set: G] &
          ~~ odd #|G| -> (forall v : G, #|N(v)| <= 2) ->
            forall A : {set G}, stable A -> stable (~: A) -> \sum_(v in A) g v <= val [set: G]].
