(** * On-line choice number and choice number

Zhu, "On-line list colouring of graphs", Electron. J. Combin. 16 (2009); Open Problem Garden,
bounding_the_on_line_choice_number_in_terms_of_the_choice_number.

The choice number ch(G) is the minimum k such that, for every assignment of lists of at least k
colours to the vertices, G has a proper colouring from these lists.  The on-line choice number is
defined by a game, where each vertex has k tokens at the beginning.  At each turn, the first player
marks a nonempty set S of uncoloured vertices, which lose one token each, and the second player
colours a stable subset of S (with a new colour).  The second player loses if some uncoloured vertex
has no token left at the beginning of a turn, and wins when all vertices are coloured.  The on-line
choice number ch^OL(G) is the minimum k such that the second player has a winning strategy.

Question: are there graphs G for which ch^OL(G) - ch(G) is arbitrarily large?

The proposition states the positive answer: for every M, there is a graph G such that ch^OL(G) -
ch(G) >= M.

Encoding.  Graphs are finite and simple.  "ch(G) = m" and "ch^OL(G) = m" are relations between G and
m.  The subtraction is that of natural numbers, as ch(G) <= ch^OL(G).  The game is defined by
recursion on a bound on the number of turns, which is large enough not to matter, as each turn
removes a token of an uncoloured vertex. *)

From GraphTheory Require Import digraph sgraph dom.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** The set [A] of vertices can be coloured on line, [f v] being the number of times that [v]
    may be presented: at each turn, the opponent presents a nonempty set [M] of uncoloured
    vertices, and a stable subset [I] of [M] is coloured.  The number of turns is at most
    [n]. *)
Fixpoint paintable_within (G : sgraph) (n : nat) (A : {set G}) (f : G -> nat)
    {struct n} : bool :=
  match n with
  | 0 => A == set0
  | n'.+1 =>
      (A == set0) ||
      ([forall v, (v \in A) ==> (0 < f v)] &&
       [forall M : {set G},
          (M \subset A) ==> (M != set0) ==>
          [exists I : {set G},
             [&& I \subset M, stable I &
                 @paintable_within G n' (A :\: I)
                   (fun v => if v \in M then (f v).-1 else f v)]]])
  end.

(** [G] is [f]-paintable (the number of turns is large enough not to matter). *)
Definition paintable (G : sgraph) (f : G -> nat) : Prop :=
  @paintable_within G (\sum_(v in [set: G]) (f v).+1) [set: G] f.

(** [G] is [k]-paintable (on-line [k]-choosable). *)
Definition k_paintable (G : sgraph) (k : nat) : Prop :=
  @paintable G (fun _ : G => k).

(** The on-line choice number (paint number) of [G] is [m]. *)
Definition online_choice_number (G : sgraph) (m : nat) : Prop :=
  k_paintable G m /\ (forall k, k_paintable G k -> m <= k).

(** ** Statement *)

Definition OPG_online_choice_number_minus_choice_unbounded : Prop :=
  forall M : nat, exists (G : sgraph) (ch chol : nat),
    [/\ choice_number G ch, online_choice_number G chol & M <= chol - ch].
