(** * Algorithm for graph homomorphisms

Fomin, Heggernes, Kratsch, "Exact Algorithms for Graph Homomorphisms", Theory Comput. Syst. 41
(2007); Open Problem Garden, algorithm_for_graph_homomorphisms.

A homomorphism from a graph G to a graph H is a map from V(G) to V(H) that sends adjacent
vertices to adjacent vertices.

Question: is there an algorithm that decides, for input graphs G and H, whether there exists a
homomorphism from G to H in time O(c^(|V(G)| + |V(H)|)) for some constant c?

The proposition states the positive answer.

Encoding.  Algorithms are programs of the small language defined below, whose interpreter counts
steps.  The program receives the adjacency matrices of G and H, which are simple graphs.  The number
of steps is polynomially related to the running time on usual machines, which is enough since c is
arbitrary; c is an integer for the same reason.  The bound O(c^(|V(G)| + |V(H)|)) is written
a c^(|V(G)| + |V(H)|) + b. *)

From GraphTheory Require Import digraph sgraph.
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

(** [p] decides [P]. *)
Definition decides_on (T : Type) (enc : T -> data) (P : T -> Prop) (p : prog) : Prop :=
  forall x : T, prog_run p (enc x) = Dnat 1 <-> P x.

(** The encoding of a list. *)
Definition enc_list (ds : seq data) : data := foldr Dcons Dnil ds.

(** The encoding of a boolean. *)
Definition enc_bool (b : bool) : data := Dnat b.

(** The encoding of a graph: its adjacency matrix. *)
Definition enc_graph (G : sgraph) : data :=
  enc_list [seq enc_list [seq enc_bool (i -- j) | j <- enum G] | i <- enum G].

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** ** Definitions specific to the conjecture *)

(** The encoding of a pair of graphs. *)
Definition enc_hom (GH : sgraph * sgraph) : data :=
  Dpair (enc_graph GH.1) (enc_graph GH.2).

(** ** Statement *)

(** Positive answer to the question. *)
Definition OPG_graph_homomorphism_single_exponential_algorithm : Prop :=
  exists (c : nat) (p : prog) (a b : nat),
    [/\ 1 < c,
        decides_on enc_hom (fun GH => homs_to GH.1 GH.2) p &
        forall GH : sgraph * sgraph,
          prog_cost p (enc_hom GH) <= a * c ^ (#|GH.1| + #|GH.2|) + b ].
