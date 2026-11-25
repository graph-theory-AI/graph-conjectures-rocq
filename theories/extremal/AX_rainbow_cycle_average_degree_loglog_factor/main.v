(** * Average degree that guarantees a rainbow cycle

Alon, Bucić, Sauermann, Zakharov, Zamir, "Essentially tight bounds for rainbow cycles in proper
edge-colourings", arXiv:2309.04460, Question 10.1 (2309.04460__00).

An edge colouring is proper if the edges at each vertex have distinct colours, and a cycle is
rainbow if its edges have distinct colours.  It is known that, for some constant C > 0, every
properly edge-coloured graph on n >= 3 vertices with average degree at least C log n log log n
contains a rainbow cycle.

Question: is the factor log log n necessary, or does average degree at least C log n suffice for
some constant C?

The proposition states that it does not suffice, as suggested by the authors: for every constant C,
there is a properly edge-coloured graph on n >= 3 vertices, with average degree at least C log n and
without rainbow cycle.

Encoding.  Graphs are finite and simple, and colours are natural numbers.  The average degree is
2|E(G)|/n.  The logarithm is in base 2 and rounded down, and C is a natural number: this is
equivalent, as C is arbitrary and n >= 2. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types (s c : seq T) (x y : T).

(** The list of the pairs of consecutive elements of the cyclic sequence [c]: the edges of a
    closed walk. *)
Definition seq_cycle_edge_list c : seq {set T} :=
  map (fun p : T * T => [set p.1; p.2]) (zip c (rot 1 c)).

End Sequences.

Section Cycles.
Variables (T : eqType) (r : rel T).
Implicit Types c d : seq T.

(** [c] is a cycle (without repetition, of length at least 3) of the relation [r]. *)
Definition seq_cycle c : bool := ucycleb r c && (2 < size c).

End Cycles.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** ** Definitions specific to the conjecture *)

(** [c] is a rainbow cycle of [G] for the edge colouring [col]. *)
Definition rainbow_cycle (G : sgraph) (C : eqType) (col : {set G} -> C) (c : seq G) : bool :=
  seq_cycle (--) c && uniq (map col (seq_cycle_edge_list c)).

(** ** Statement *)

Definition AX_rainbow_cycle_average_degree_loglog_factor : Prop :=
  forall C : nat, exists (G : sgraph) (col : {set G} -> nat),
    [/\ 3 <= #|G|, proper_edge_coloring col,
        C * trunc_log 2 #|G| * #|G| <= 2 * #|E(G)| &
        forall c : seq G, ~~ rainbow_cycle col c].
