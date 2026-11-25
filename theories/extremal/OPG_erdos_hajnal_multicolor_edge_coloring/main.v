(** * Multicolour Erdős-Hajnal conjecture

Erdős, Hajnal; Fox, Grinshpun, Pach, "The Erdős-Hajnal conjecture for rainbow triangles",
J. Combin. Theory Ser. B 111 (2015); Open Problem Garden, multicolour_erdos_hajnal_conjecture.

Conjecture: for every k >= 2 and every colouring χ of the edges of K_k with m colours, there is
ε > 0 such that every colouring of the edges of K_n contains either k vertices whose edges are
coloured according to χ, or at least n^ε vertices whose edges are coloured with at most m - 1
colours.

Encoding.  The colourings of K_n use the same m colours as χ, which is implicit: with arbitrarily
many colours, a colouring of K_n with distinct colours is a counterexample for most χ.  All m
colours are used by χ; this is not a restriction, as otherwise χ can be extended to a colouring of
a larger complete graph that uses all of them.  It is assumed that m >= 2: if m = 1, the
conclusion fails for 2 <= n < k since a set of two vertices has a colour.  Colourings are symmetric
functions, whose values on the diagonal are not used.  The exponent is ε = a/b with a, b > 0, and
the inequality |A| >= n^ε is written n^a <= |A|^b. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions specific to the conjecture *)

(** The colouring [chi] of the edges of [K_k] uses all [m] colours. *)
Definition uses_all_colours (k m : nat) (chi : 'I_k -> 'I_k -> 'I_m) : Prop :=
  forall c : 'I_m, exists i j : 'I_k, i != j /\ chi i j = c.

(** The colouring [col] of [K_n] contains [k] vertices whose edges are coloured according to
    [chi]. *)
Definition contains_pattern (n k m : nat) (chi : 'I_k -> 'I_k -> 'I_m)
    (col : 'I_n -> 'I_n -> 'I_m) : Prop :=
  exists g : 'I_k -> 'I_n,
    injective g /\ forall i j : 'I_k, i != j -> col (g i) (g j) = chi i j.

(** The colours of the edges between vertices of [A]. *)
Definition palette_on (n m : nat) (col : 'I_n -> 'I_n -> 'I_m) (A : {set 'I_n}) : {set 'I_m} :=
  [set c : 'I_m | [exists x : 'I_n, [exists y : 'I_n,
    [&& x \in A, y \in A, x != y & col x y == c]]]].

(** ** Statement *)

Definition OPG_erdos_hajnal_multicolor_edge_coloring : Prop :=
  forall (k m : nat) (chi : 'I_k -> 'I_k -> 'I_m),
    2 <= k -> 2 <= m ->
    (forall i j : 'I_k, chi i j = chi j i) -> uses_all_colours chi ->
    exists a b : nat, 0 < a /\ 0 < b /\
      forall (n : nat) (col : 'I_n -> 'I_n -> 'I_m),
        (forall x y : 'I_n, col x y = col y x) ->
        contains_pattern chi col \/
        exists A : {set 'I_n}, n ^ a <= #|A| ^ b /\ #|palette_on col A| <= m - 1.
