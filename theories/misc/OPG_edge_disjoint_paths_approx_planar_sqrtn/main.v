(** * Approximation ratio for the Maximum Edge Disjoint Paths problem

Bentz, "Edge disjoint paths and max integral multiflow/min multicut theorems in planar graphs",
Electronic Notes in Discrete Mathematics 22 (2005); Open Problem Garden,
approximation_ratio_for_maximum_edge_disjoint_paths_problem.

Given a graph G with n vertices and a list of pairs of vertices (the demands), the Maximum Edge
Disjoint Paths problem (MaxEDP) is to join as many demands as possible by edge-disjoint paths.
Bentz gave a polynomial algorithm with approximation ratio O(√n).

Question: can the approximation ratio O(√n) be improved for MaxEDP in planar graphs, or can an
inapproximability result stronger than APX-hardness be proved?

The proposition states a positive answer to the first part: there are a function ρ with
ρ(n) = o(√n) and a polynomial algorithm which, for every planar graph G on n vertices and every
list of demands, joins at least OPT / ρ(n) demands by edge-disjoint paths, where OPT is the maximum.

Encoding.  The second part of the question, which has no definite meaning, is not stated.
Polynomial-time algorithms are programs of the small language defined below, with a polynomial
number of steps.  The program receives the adjacency matrix of a simple graph G and the demands, as
pairs of indices of vertices.  If G is planar (without minor K_5 or K_3,3), it returns a list of
paths in the order of the demands, where the empty list means that the demand is not joined.  The
number of steps is bounded for all graphs, which is equivalent, as a program can be stopped after a
given number of steps.  A demand with two equal ends is joined by a path without edges; such
demands do not change the approximation ratio. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types s : seq T.

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

End Sequences.

Section Paths.
Variable G : diGraph.
Implicit Types (p : seq G) (X Y : {set G}).

(** [p] is a path (nonempty, without repetition). *)
Definition seq_simple_path p : bool := if p is x :: q then path (--) x q && uniq p else false.

(** [p] is a path from a vertex of [X] to a vertex of [Y]. *)
Definition seq_path_between X Y p : bool :=
  if p is x :: q then [&& x \in X, last x q \in Y & seq_simple_path p] else false.

End Paths.

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

(** ** Definitions copied from GraphLib/packing.v *)

(** [P] joins some demands (pairs of vertices) of the list [D] by edge-disjoint paths: its [i]-th
    element is a path between the ends of the [i]-th demand, or the empty list if this demand is
    not joined. *)
Definition edp_solution (G : sgraph) (D : seq (G * G)) (P : seq (seq G)) : bool :=
  [&& size P == size D,
      all (fun x : (G * G) * seq G =>
             nilp x.2 || seq_path_between [set x.1.1] [set x.1.2] x.2) (zip D P)
    & uniq (flatten [seq seq_edge_list p | p <- P])].

(** The number of demands that are joined. *)
Definition edp_value (G : sgraph) (P : seq (seq G)) : nat := count (fun p => ~~ nilp p) P.

(** The instances: a graph and a list of demands. *)
Definition edp_input : Type := {G : sgraph & seq (G * G)}.

(** The encoding of an instance. *)
Definition enc_edp (x : edp_input) : data :=
  Dpair (enc_graph (projT1 x))
        (enc_list [seq Dpair (Dnat (enum_rank d.1)) (Dnat (enum_rank d.2))
                  | d <- projT2 x]).

(** The encoding of a list of paths. *)
Definition enc_paths (G : sgraph) (P : seq (seq G)) : data :=
  enc_list [seq enc_list [seq Dnat (enum_rank v) | v <- p] | p <- P].

(** The output encodes a solution whose value is at least the optimum divided by [rho n], where
    [n] is the number of vertices. *)
Definition edp_approximation (rho : nat -> nat) (x : edp_input) (out : data) : Prop :=
  exists P : seq (seq (projT1 x)),
    [/\ out = enc_paths P,
        edp_solution (projT2 x) P
      & forall Q : seq (seq (projT1 x)),
          edp_solution (projT2 x) Q -> edp_value Q <= rho #|projT1 x| * edp_value P].

(** ** Definitions copied from GraphLib/topological.v *)

(** [G] is planar: it has no minor [K_5] or [K_3,3]. *)
Definition planar (G : sgraph) : Prop :=
  ~ minor G 'K_5 /\ ~ minor G (KB 3 3).

(** ** Definitions specific to the conjecture *)

(** [rho] is o(√n). *)
Definition little_o_sqrt (rho : nat -> nat) : Prop :=
  forall c : nat, exists N : nat, forall n : nat, N <= n -> c * (rho n) ^ 2 <= n.

(** ** Statement *)

(** The ratio O(√n) can be improved. *)
Definition OPG_edge_disjoint_paths_approx_planar_sqrtn : Prop :=
  exists rho : nat -> nat,
    little_o_sqrt rho /\
    polytime_outputs enc_edp (fun x => planar (projT1 x)) (edp_approximation rho).
