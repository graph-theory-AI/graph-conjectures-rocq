(** * PTAS for feedback arc set in tournaments

Ailon, Alon, "Hardness of fully dense problems", Inform. and Comput. 205 (2007); Open Problem
Garden, ptas_for_feedback_arc_set_in_tournaments.

A tournament is an orientation of a complete graph.  A feedback arc set of a digraph is a set of
arcs whose removal leaves an acyclic digraph; the problem is to find one of minimum size.  A
polynomial time approximation scheme (PTAS) is an algorithm that takes an instance and a parameter
ε > 0 and produces, in polynomial time, a solution within a factor 1 + ε of the optimum.

Question: is there a polynomial time approximation scheme for the feedback arc set problem for
the class of tournaments?

The proposition states the positive answer.

Encoding.  The parameter ε is a positive rational p/q, and the polynomial that bounds the running
time depends on ε.  Polynomial-time algorithms are programs of the small language defined below,
with a polynomial number of steps.  The program receives p, q and the adjacency matrix of a digraph
and, if it is a tournament, returns a feedback arc set as a list of pairs of indices of vertices.
The number of steps is bounded for all digraphs, which is equivalent, as a program can first check
that the digraph is a tournament. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Data. *)
Inductive data : Type :=
| Dnat  of nat
| Dpair of data & data
| Dnil
| Dcons of data & data.

(** The size of [d] (numbers are in unary). *)
Fixpoint data_size (d : data) : nat :=
  match d with
  | Dnat n => n.+1
  | Dpair a b => (data_size a + data_size b).+1
  | Dnil => 1
  | Dcons a b => (data_size a + data_size b).+1
  end.

(** Equality of data. *)
Fixpoint data_eq (a b : data) : bool :=
  match a, b with
  | Dnat m, Dnat n => m == n
  | Dpair x y, Dpair u v => data_eq x u && data_eq y v
  | Dnil, Dnil => true
  | Dcons x y, Dcons u v => data_eq x u && data_eq y v
  | _, _ => false
  end.

(** Programs: identity, constants, composition, pairs, lists, equality test, arithmetic,
    iteration and recursion on lists. *)
Inductive prog : Type :=
| Pid | Pconst of data
| Pcomp of prog & prog          (* left, then right *)
| Ppair of prog & prog | Pfst | Psnd
| Pcons of prog & prog
| Pcase of prog & prog         (* right on (Dpair a b) if the input is Dcons a b, else left *)
| Peq                           (* Dpair a b => Dnat (data_eq a b) *)
| Padd | Pmul | Ppred
| Pnatrec of prog               (* Dpair (Dnat n) seed => iterate the body n times on seed *)
| Pfold of prog & prog.

(** The result of a program and its number of steps. *)
Fixpoint prog_eval (p : prog) (d : data) : data * nat :=
  match p with
  | Pid => (d, 1)
  | Pconst k => (k, 1)
  | Pcomp p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 r1.1 in
      (r2.1, (r1.2 + r2.2).+1)
  | Ppair p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 d in
      (Dpair r1.1 r2.1, (r1.2 + r2.2).+1)
  | Pfst => (if d is Dpair a _ then a else d, 1)
  | Psnd => (if d is Dpair _ b then b else d, 1)
  | Pcons p1 p2 =>
      let r1 := prog_eval p1 d in let r2 := prog_eval p2 d in
      (Dcons r1.1 r2.1, (r1.2 + r2.2).+1)
  | Pcase p1 p2 =>
      match d with
      | Dcons a b => let r := prog_eval p2 (Dpair a b) in (r.1, r.2.+1)
      | _ => let r := prog_eval p1 d in (r.1, r.2.+1)
      end
  | Peq => (if d is Dpair a b then Dnat (data_eq a b) else Dnat 0, data_size d)
  | Padd => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a + b) else Dnat 0, data_size d)
  | Pmul => (if d is Dpair (Dnat a) (Dnat b) then Dnat (a * b) else Dnat 0, data_size d)
  | Ppred => (if d is Dnat n then Dnat n.-1 else Dnat 0, 1)
  | Pnatrec body =>
      match d with
      | Dpair (Dnat n) seed =>
          (fix N (n : nat) (acc : data) (c : nat) : data * nat :=
             match n with
             | 0 => (acc, c.+1)
             | m.+1 => N m (prog_eval body acc).1 (c + (prog_eval body acc).2).+1
             end) n seed 0
      | _ => (d, 1)
      end
  | Pfold pn pc =>
      (fix F (d : data) : data * nat :=
         match d with
         | Dcons a b =>
             (  (prog_eval pc (Dpair a (F b).1)).1,
                ((F b).2 + (prog_eval pc (Dpair a (F b).1)).2).+1 )
         | _ => ((prog_eval pn d).1, (prog_eval pn d).2.+1)
         end) d
  end.

(** The result of [p] on [d]. *)
Definition prog_run  (p : prog) (d : data) : data := (prog_eval p d).1.

(** The number of steps of [p] on [d]. *)
Definition prog_cost (p : prog) (d : data) : nat  := (prog_eval p d).2.

(** [p] is polynomial on the encodings of the elements of [T]. *)
Definition polytime_on (T : Type) (enc : T -> data) (p : prog) : Prop :=
  exists c k : nat, forall x : T, prog_cost p (enc x) <= c * (data_size (enc x)) ^ k + c.

(** The encoding of a list. *)
Definition enc_list (ds : seq data) : data := foldr Dcons Dnil ds.

(** The encoding of a boolean. *)
Definition enc_bool (b : bool) : data := Dnat b.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is a tournament: it has no loop, and exactly one arc between any two distinct vertices. *)
Definition tournament (D : diGraph) : Prop :=
  irreflexive (@edge_rel D) /\ forall x y : D, (x != y) = (x -- y) (+) (y -- x).

(** The set of arcs. *)
Definition arcs (D : diGraph) : {set D * D} := [set p | p.1 -- p.2].

(** Deletion of the arcs of [F]. *)
Definition del_arcs (D : diGraph) (F : {set D * D}) : diGraph :=
  DiGraph (fun u v : D => (u -- v) && ((u, v) \notin F)).

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The minimum size of a set of arcs that meets all directed cycles. *)
Definition feedback_arc_number (D : diGraph) : nat :=
  #|[arg min_(F < [set: D * D] | acyclic (del_arcs F)) #|F|]|.

(** ** Definitions specific to the conjecture *)

(** The encoding of a digraph: its adjacency matrix. *)
Definition enc_digraph (D : diGraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum D] | i <- enum D].

(** The encoding of the input: the parameter [p / q] and a digraph. *)
Definition enc_fas (p q : nat) (D : diGraph) : data :=
  Dpair (Dpair (Dnat p) (Dnat q)) (enc_digraph D).

(** The encoding of a list of arcs. *)
Definition enc_arcs (D : diGraph) (F : seq (D * D)) : data :=
  enc_list [seq Dpair (Dnat (enum_rank a.1)) (Dnat (enum_rank a.2)) | a <- F].

(** The output encodes a feedback arc set of [D] whose size is at most [1 + p / q] times the
    minimum. *)
Definition fas_approximation (p q : nat) (D : diGraph) (out : data) : Prop :=
  exists F : seq (D * D),
    [/\ out = enc_arcs F,
        {subset F <= arcs D},
        acyclic (del_arcs [set:: F])
      & q * size F <= (q + p) * feedback_arc_number D].

(** ** Statement *)

(** Positive answer to the question. *)
Definition OPG_tournament_feedback_arc_set_ptas : Prop :=
  exists A : prog, forall p q : nat, 0 < p -> 0 < q ->
    polytime_on (enc_fas p q) A /\
    forall D : diGraph,
      tournament D -> fas_approximation p q D (prog_run A (enc_fas p q D)).
