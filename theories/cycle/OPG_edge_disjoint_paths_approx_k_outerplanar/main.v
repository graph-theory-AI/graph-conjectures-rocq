(** * Approximation ratio for k-outerplanar graphs

Bentz, "Disjoint paths in sparse graphs", Discrete Applied Mathematics 157 (2009); Open Problem
Garden, approximation_ratio_for_k_outerplanar_graphs.

Given a graph G and a list of pairs of vertices (the demands), the maximum edge disjoint paths
problem (MaxEDP) is to join as many demands as possible by edge-disjoint paths.  The maximum integer
multiflow problem (MaxIMF) is the variant where the edges have capacities, and where a demand can be
joined by several paths.  In the linear relaxation of MaxEDP, the paths have nonnegative weights,
the total weight of the paths that join a demand is at most 1, and so is the total weight of the
paths that contain an edge.  The integrality gap is the maximum ratio between the optima of the
relaxation and of MaxEDP.

A graph is k-outerplanar if it has a plane drawing where no vertex remains after removing k times
the vertices of the outer face.

Question: is the approximation ratio (integrality gap) for MaxEDP or MaxIMF bounded by a constant in
k-outerplanar graphs or in graphs of bounded treewidth?

The proposition states the positive answer for MaxEDP and bounded treewidth: for every w there is a
constant c such that, in the graphs of treewidth at most w, the integrality gap of MaxEDP is at
most c, and some polynomial algorithm joins at least OPT / c demands by edge-disjoint paths, where
OPT is the maximum.

Encoding.  The treewidth of a k-outerplanar graph is at most 3k - 1, so the case of k-outerplanar
graphs is included.  Graphs are finite and simple, which is no restriction, as edges can be
subdivided.  For the integrality gap, MaxIMF is the special case where an edge is replaced by paths
of length 2, as many as its capacity, and where demands are repeated.  The weights of the linear
relaxation are rational.  A demand with two equal ends is joined by a path without edges.

Polynomial-time algorithms are programs of the small language defined below, with a polynomial
number of steps.  The program receives the adjacency matrix of the graph and the demands, as pairs
of indices of vertices.  It returns a list of paths in the order of the demands, where the empty
list means that the demand is not joined.  The result matters only if the treewidth is at most w,
but the number of steps is bounded for all graphs, which is equivalent, as a program can be stopped
after a given number of steps. *)

From GraphTheory Require Import digraph sgraph treewidth.
From mathcomp Require Import boot order algebra.

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

(** ** Definitions copied from GraphLib/minor.v *)

(** The treewidth of [G] is at most [k] (the width of a decomposition is, in GraphTheory, the
    maximum size of a bag). *)
Definition treewidth_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

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

(** ** Definitions specific to the conjecture *)

Section Relaxation.
Variables (G : sgraph) (D : seq (G * G)).
Local Open Scope ring_scope.

(** A solution of the linear relaxation: a list of triples [(i, p, r)], where [p] is a path between
    the ends of the [i]-th demand and [r] is its weight.  The total weight is at most 1 for each
    demand and for each edge. *)
Definition fractional_edp_solution (L : seq ('I_(size D) * seq G * rat)) : Prop :=
  [/\ forall i p r, (i, p, r) \in L ->
        0 <= r /\
        seq_path_between [set (tnth (in_tuple D) i).1] [set (tnth (in_tuple D) i).2] p,
      forall i, \sum_(t <- L | t.1.1 == i) t.2 <= 1
    & forall e : {set G}, \sum_(t <- L | e \in seq_edge_list t.1.2) t.2 <= 1].

(** The value of this solution. *)
Definition fractional_edp_value (L : seq ('I_(size D) * seq G * rat)) : rat :=
  \sum_(t <- L) t.2.

(** The integrality gap is at most [c]. *)
Definition integrality_gap_le (c : nat) : Prop :=
  forall L, fractional_edp_solution L ->
    exists P : seq (seq G),
      edp_solution D P /\ fractional_edp_value L <= (c * edp_value P)%:R.

End Relaxation.

(** ** Statement *)

Definition OPG_edge_disjoint_paths_approx_k_outerplanar : Prop :=
  forall w : nat, exists c : nat,
    (forall (G : sgraph) (D : seq (G * G)), treewidth_le G w -> integrality_gap_le D c) /\
    polytime_outputs enc_edp (fun x => treewidth_le (projT1 x) w) (edp_approximation (fun=> c)).
