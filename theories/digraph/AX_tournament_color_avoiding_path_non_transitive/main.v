(** * Color-avoiding paths in non-transitive tournaments

Fox, Sudakov, Wigderson, "Color-avoiding directed paths in tournaments", 2025,
arXiv:2512.10438, Problem 5.1 (2512.10438__00).

A q-edge-coloured tournament is a tournament where each arc has one of q colours (the colouring
need not be proper).  A directed path is color-avoiding if its arcs use at most q-1 of the q
colours.  Let f_{q,q-1}(N) be the minimum, over all q-edge-colourings of the transitive tournament
on N vertices, of the number of vertices of a longest color-avoiding directed path.

Problem 5.1: for some integers q >= 4 and N, does there exist a non-transitive
q-edge-coloured tournament on N vertices whose longest color-avoiding path has strictly fewer
than f_{q,q-1}(N) vertices?  The proposition states a positive answer.

Encoding.  Tournaments are digraphs of GraphTheory ([diGraph]: a finite type of vertices with
a boolean relation [--]) satisfying the predicate [tournament].  A colouring is a function
[chi] on all couples of vertices, whose values matter only on the arcs.  A path uses at most
q-1 colours if and only if it avoids some colour.  Numbers of vertices of longest paths, and
f_{q,q-1}(N), are given by relations ("[n] is the value of ...") instead of functions. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Paths.
Variable G : diGraph.
Implicit Types p : seq G.

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

End Paths.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The transitive tournament on [n] vertices. *)
Definition transitive_tournament (n : nat) : diGraph := DiGraph [rel u v : 'I_n | u < v].

(** The vertices [x :: s] form a directed path (from [x] to [last x s], of length [size s]). *)
Definition dipath (D : diGraph) (x : D) (s : seq D) : bool := seq_simple_path (x :: s).

(** ** Definitions specific to the conjecture *)

(** The walk [x :: s] uses no arc of colour [c]. *)
Definition avoiding (D : diGraph) (q : nat) (chi : D -> D -> 'I_q) (c : 'I_q)
    (x : D) (s : seq D) : bool :=
  path (fun u v : D => (u -- v) && (chi u v != c)) x s.

(** Some colour is not used by the walk [x :: s]. *)
Definition color_avoiding (D : diGraph) (q : nat) (chi : D -> D -> 'I_q)
    (x : D) (s : seq D) : bool :=
  [exists c : 'I_q, avoiding chi c x s].

(** The color-avoiding directed paths have at most [n] vertices. *)
Definition avoids_bound (D : diGraph) (q : nat) (chi : D -> D -> 'I_q) (n : nat) : Prop :=
  forall (x : D) (s : seq D), dipath x s -> color_avoiding chi x s -> size s < n.

(** The longest color-avoiding directed paths have [n] vertices. *)
Definition longest_avoiding_vertices (D : diGraph) (q : nat) (chi : D -> D -> 'I_q)
    (n : nat) : Prop :=
  avoids_bound chi n /\
  exists (x : D) (s : seq D), [/\ dipath x s, color_avoiding chi x s & size (x :: s) = n].

(** f_{q,q-1}(N) = n: for each [q]-colouring, the transitive tournament on [N] vertices has a
    color-avoiding directed path with at least [n] vertices, and, for some colouring, the
    longest ones have [n] vertices. *)
Definition transitive_minimum_is (q N n : nat) : Prop :=
  let T := transitive_tournament N in
  (forall chi : T -> T -> 'I_q,
     exists (x : T) (s : seq T),
       [/\ dipath x s, color_avoiding chi x s & n <= size (x :: s)]) /\
  exists chi : T -> T -> 'I_q, longest_avoiding_vertices chi n.

(** ** Statement *)

(** For some q >= 4 and N, the longest color-avoiding paths of some non-transitive q-edge-coloured
    tournament on N vertices have fewer than f_{q,q-1}(N) vertices. *)
Definition AX_tournament_color_avoiding_path_non_transitive : Prop :=
  exists (q N : nat) (T : diGraph) (chi : T -> T -> 'I_q) (m n : nat),
    [/\ 4 <= q, tournament T, #|T| = N & ~ transitive (@edge_rel T)] /\
    [/\ longest_avoiding_vertices chi m, transitive_minimum_is q N n & m < n].
