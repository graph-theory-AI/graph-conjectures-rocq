(** * Colouring k-connected graphs of maximal local connectivity k

Aboulker, Brettell, Havet, Marx, Trotignon, "Colouring graphs with constraints on connectivity",
arXiv:1505.01616, Question 1.7 (1505.01616__00).

The local connectivity of two distinct vertices x and y is the maximum number of internally
vertex-disjoint paths from x to y.  A graph has maximal local connectivity k if the local
connectivity of any two distinct vertices is at most k.

Question 1.7: for fixed k >= 4, is there a polynomial-time algorithm that, given a k-connected
graph G with maximal local connectivity k, finds a k-colouring of G, or determines that none exists?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  Polynomial-time algorithms are programs of the small
language defined below, with a polynomial number of steps.  The program receives the adjacency
matrix of a graph G, and returns the number 0 if G is not k-colourable, and otherwise a list of
numbers which are the colours modulo k of the vertices, in the order of the rows of the matrix.  The
number of steps is bounded for all graphs, which is equivalent, as a program can be stopped after a
given number of steps. *)

From GraphTheory Require Import digraph sgraph coloring connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** The local connectivity of any two distinct vertices is at most [k]: every set of internally
    disjoint paths between them has at most [k] elements. *)
Definition local_connectivity_le (G : sgraph) (k : nat) : Prop :=
  forall (x y : G) (P : {set IPath x y}),
    x != y ->
    (forall p q : IPath x y, p \in P -> q \in P -> p != q -> independent p q) ->
    #|P| <= k.

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

(** Some polynomial program satisfies [Spec] on the elements of [Class]. *)
Definition polytime_outputs (T : Type) (enc : T -> data)
    (Class : T -> Prop) (Spec : T -> data -> Prop) : Prop :=
  exists p : prog, polytime_on enc p /\
    forall x : T, Class x -> Spec x (prog_run p (enc x)).

(** The encoding of a list. *)
Definition enc_list (ds : seq data) : data := foldr Dcons Dnil ds.

(** The encoding of a boolean. *)
Definition enc_bool (b : bool) : data := Dnat b.

(** The encoding of a graph: its adjacency matrix. *)
Definition enc_graph (G : sgraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum G] | i <- enum G].

(** ** Definitions specific to the conjecture *)

(** The natural number at position [i] in the list encoded by [d] (0 if there is none). *)
Fixpoint data_nth_nat (d : data) (i : nat) : nat :=
  match d, i with
  | Dcons (Dnat n) _, 0 => n
  | Dcons _ rest, j.+1 => data_nth_nat rest j
  | Dnat n, 0 => n
  | _, _ => 0
  end.

(** The colour of [v] in the result [out], modulo [k]. *)
Definition output_colour (G : sgraph) (k : nat) (out : data) (v : G) : nat :=
  data_nth_nat out (enum_rank v) %% k.

(** The result [out] is 0 and [G] is not [k]-colourable, or it gives a proper [k]-colouring
    of [G]. *)
Definition output_k_colouring_or_none (k : nat) (G : sgraph) (out : data) : Prop :=
  (out = Dnat 0 /\ ~ χ([set: G]) <= k) \/
  (0 < k /\ forall x y : G, x -- y -> output_colour k out x != output_colour k out y).

(** ** Statement *)

Definition AX_k_coloring_maximal_local_connectivity_k : Prop :=
  forall k : nat, 4 <= k ->
    polytime_outputs enc_graph
      (fun G : sgraph => k.-connected G /\ local_connectivity_le G k)
      (output_k_colouring_or_none k).
