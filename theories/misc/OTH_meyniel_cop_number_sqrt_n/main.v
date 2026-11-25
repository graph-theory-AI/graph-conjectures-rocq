(** * Meyniel's conjecture on the cop number

Meyniel (1985), reported by Frankl, "Cops and robbers in graphs with large girth and Cayley
graphs", Discrete Applied Mathematics 17 (1987); id meyniels-conjecture.

In the game of cops and robbers on a graph, k cops choose vertices, then the robber chooses a
vertex.  The two sides move alternately, the cops first: each piece stays at its vertex or moves
to a neighbour.  The cops win if one of them reaches the vertex of the robber.  The cop number
c(G) is the minimum k such that k cops have a winning strategy on G.

Conjecture: there is a constant C such that c(G) <= C √n for every connected graph G on n
vertices.

Encoding.  The graphs are nonempty.  Winning means capturing the robber in at most t rounds, for
some t that depends only on the graph and the number of cops.  The square root is rounded up,
which only changes the constant C. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sqrt_ceil_ex (n : nat) : exists s : nat, n <= s ^ 2.
Proof. by exists n; rewrite expnS expn1; case: n => // m; rewrite leq_pmulr. Qed.

(** The ceiling of the square root of [n]: the least [s] such that [n <= s ^ 2]. *)
Definition sqrt_ceil (n : nat) : nat := ex_minn (sqrt_ceil_ex n).

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

(** The cop number of [G] is at most [k]. *)
Definition cop_number_le (k : nat) : Prop := exists j : nat, (j <= k)%N /\ cops_win j.

End CopsAndRobbers.

(** ** Statement *)

Definition OTH_meyniel_cop_number_sqrt_n : Prop :=
  exists C : nat,
    forall G : sgraph,
      0 < #|G| -> connected [set: G] ->
      cop_number_le G (C * sqrt_ceil #|G|).
