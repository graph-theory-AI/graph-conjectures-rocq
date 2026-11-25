(** * Additive approximation of the chromatic number of triangle-free graphs

Dvořák, Kawarabayashi, "Additive non-approximability of chromatic number in proper minor-closed
classes", arXiv:1707.03888, open question (1707.03888__00).

A class of graphs is minor-closed if it contains all minors of its members; it is proper if it does
not contain all graphs.

Question: does there exist α >= 0 such that for every proper minor-closed class, the chromatic
number of the triangle-free graphs G of the class can be approximated in polynomial time within
additive error α, i.e. an integer c such that χ(G) <= c <= χ(G) + α can be computed?

The proposition states the positive answer.

Encoding.  Graphs are finite and simple.  The class is any class C such that some graph is a minor
of no member of C.  This is equivalent: a proper minor-closed class has this property (take a graph
that is not in the class), and C is included in a proper minor-closed class.  Polynomial-time
algorithms are programs of the small language defined below, with a polynomial number of steps.
The program receives the adjacency matrix of a graph G, and returns c if G is a triangle-free graph
of the class.  The number of steps is bounded for all graphs, which is equivalent, as a program can
be stopped after a given number of steps. *)

From GraphTheory Require Import digraph sgraph coloring minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

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

(** The natural number encoded by [d] (0 if there is none). *)
Definition data_nat_value (d : data) : nat :=
  if d is Dnat n then n else 0.

(** The encoding of a graph: its adjacency matrix. *)
Definition enc_graph (G : sgraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum G] | i <- enum G].

(** ** Definitions copied from GraphLib/minor.v *)

(** The class [C] excludes some graph as a minor. *)
Definition excludes_a_minor (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

(** ** Definitions specific to the conjecture *)

(** The result [out] is an approximation of the chromatic number of [G] within additive error
    [alpha]. *)
Definition additive_chromatic_output (alpha : nat) (G : sgraph) (out : data) : Prop :=
  χ([set: G]) <= data_nat_value out /\ data_nat_value out <= χ([set: G]) + alpha.

(** ** Statement *)

Definition AX_additive_chi_approx_minor_closed_triangle_free : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop, excludes_a_minor C ->
      polytime_outputs enc_graph
        (fun G : sgraph => C G /\ triangle_free G) (additive_chromatic_output alpha).
