(** * Asymmetric list sizes in bipartite graphs

Alon, Cambie, Kang, "Asymmetric list sizes in bipartite graphs",
arXiv:2004.07457, Conjecture 7 (2004.07457__01).

A bipartite graph with parts A and B is (k_A, k_B)-choosable if, for all lists of k_A colours on the
vertices of A and of k_B colours on the vertices of B, it has a proper colouring from these lists.

Conjecture: let the positive integers Δ_A, Δ_B, k_A, k_B satisfy one of the following.
(i) Given ε > 0, we have Δ_A, Δ_B >= Δ_0 for some Δ_0 = Δ_0(ε), and k_A >= Δ_A^ε and k_B >= Δ_B^ε.
(ii) For some absolute constant C > 1, k_A >= C log Δ_B and k_B >= C log Δ_A.
(iii) Δ_A = Δ_B = Δ, and, for some absolute constant C > 0,
k_B >= C (Δ / log Δ)^(1/k_A) log Δ or k_A >= C (Δ / log Δ)^(1/k_B) log Δ.
Then any bipartite graph with parts A and B having maximum degrees at most Δ_A and Δ_B,
respectively, is (k_A, k_B)-choosable.

Encoding.  Graphs are finite and simple.  The proposition is the conjunction of the three cases.
In (ii) and (iii), the condition Δ_A, Δ_B >= 2 is added, so that log Δ_A, log Δ_B > 0: otherwise,
(ii) does not hold for Δ_A = Δ_B = 1 (take K_2 and k_A = k_B = 1).
In (i), ε = 1/q without loss of generality, and k >= Δ^ε is written Δ <= k^q.  In (iii),
k_B >= C (Δ / log Δ)^(1/k_A) log Δ is written k_B^k_A >= C^k_A Δ (log Δ)^(k_A - 1).  The constant C
is an integer, and log Δ is the integer part of the logarithm to base 2, which is equivalent up to
the value of C.  Lists have at least k_A or k_B colours, which is equivalent. *)

From GraphTheory Require Import digraph sgraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** ** Definitions specific to the conjecture *)

(** The vertices of [A] have degree at most [D]. *)
Definition max_degree_on (G : sgraph) (A : {set G}) (D : nat) : Prop :=
  forall v : G, v \in A -> #|N(v)| <= D.

(** [G] is [(kA, kB)]-choosable, with parts [A] and the complement of [A]. *)
Definition kAkB_choosable (G : sgraph) (A : {set G}) (kA kB : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, v \in A -> kA <= #|L v|) ->
    (forall v : G, v \notin A -> kB <= #|L v|) ->
    list_colorable L.

(** ** Statement *)

Definition AX_bipartite_asymmetric_list_sizes_krivelevich_alon : Prop :=
  (* (i) *)
  (forall q : nat, 0 < q ->
     exists D0 : nat,
       forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
         bipartition A ->
         max_degree_on A DA ->
         max_degree_on (~: A) DB ->
         0 < kA -> 0 < kB -> D0 <= DA -> D0 <= DB ->
         DA <= kA ^ q -> DB <= kB ^ q ->
         kAkB_choosable A kA kB)
  /\
  (* (ii) *)
  (exists2 C : nat, 1 < C &
     forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
       bipartition A ->
       max_degree_on A DA ->
       max_degree_on (~: A) DB ->
       0 < kA -> 0 < kB -> 1 < DA -> 1 < DB ->
       C * trunc_log 2 DB <= kA -> C * trunc_log 2 DA <= kB ->
       kAkB_choosable A kA kB)
  /\
  (* (iii) *)
  (exists2 C : nat, 0 < C &
     forall (G : sgraph) (A : {set G}) (D kA kB : nat),
       bipartition A ->
       max_degree_on A D ->
       max_degree_on (~: A) D ->
       0 < kA -> 0 < kB -> 1 < D ->
       (C ^ kA * D * trunc_log 2 D ^ kA.-1 <= kB ^ kA \/
        C ^ kB * D * trunc_log 2 D ^ kB.-1 <= kA ^ kB) ->
       kAkB_choosable A kA kB).
