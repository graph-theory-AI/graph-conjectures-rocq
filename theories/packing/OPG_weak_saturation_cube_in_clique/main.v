(** * Weak saturation of the cube in the clique

Morrison, Noel; Open Problem Garden, weak_saturation_of_the_cube_in_the_clique.

For graphs G and H, wsat(G,H) is the minimum number of edges in a subgraph F of G such that the
edges of E(G) ∖ E(F) can be added to F, one at a time, so that each edge completes a copy of H when
it is added.  Q_3 is the cube (the 3-dimensional hypercube).

Problem: determine wsat(K_n, Q_3).

What is stated is that wsat(K_n, Q_3) is given by a formula of the following kind: there are
integers p >= 1 and q such that wsat(K_{n+p}, Q_3) = wsat(K_n, Q_3) + q for every large enough n.
In other words, for large n, wsat(K_n, Q_3) is the sum of (q/p)n and of a periodic function of n.

Encoding.  The problem suggests no value for wsat(K_n, Q_3), so the proposition is only a proxy.  It
is incomparable with a determination of wsat(K_n, Q_3): it does not give the values, and it is not
implied by a formula of another kind.  F is a set of edges (spanning subgraphs of G are meant, and
isolated vertices do not matter).  "wsat(G,H) = m" is a relation between G, H and m.  Copies are not
necessarily induced.  wsat(K_n, Q_3) is well defined, as F = E(K_n) is allowed. *)

From GraphTheory Require Import digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Hypercube.
Variable d : nat.

(** Tuples that differ at exactly one position. *)
Definition hypercube_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.

Lemma hypercube_sym : symmetric hypercube_rel.
Proof.
move=> x y; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth y i] = [set i : 'I_d | tnth y i != tnth x i] by [].
by apply/setP => i; rewrite !inE eq_sym.
Qed.

Lemma hypercube_irrefl : irreflexive hypercube_rel.
Proof.
move=> x; rewrite /hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth x i] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE eqxx.
Qed.

(** The hypercube of dimension [d]. *)
Definition hypercube : sgraph := SGraph hypercube_sym hypercube_irrefl.

End Hypercube.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The set of edges [E] contains a copy of [H] that uses the edge [e]. *)
Definition copy_through (G H : sgraph) (E : {set {set G}}) (e : {set G}) : Prop :=
  exists f : H -> G,
    [/\ injective f,
        (forall x y : H, x -- y -> [set f x; f y] \in E)
      & exists x y : H, x -- y /\ [set f x; f y] = e].

(** [F] is a weakly [H]-saturated set of edges of [G]: the other edges of [G] can be enumerated by
    a list [s] so that each of them completes a copy of [H] when it is added to [F] and to the
    edges before it. *)
Definition weakly_saturated (G H : sgraph) (F : {set {set G}}) : Prop :=
  F \subset E(G) /\
  exists s : seq {set G},
    [/\ uniq s,
        (forall e : {set G}, (e \in s) = (e \in E(G) :\: F))
      & forall i : nat, i < size s ->
          copy_through H (F :|: [set:: take i.+1 s]) (nth set0 s i)].

(** The weak saturation number wsat(G,H) (minimum size of a weakly [H]-saturated set of edges of
    [G]) is [m]. *)
Definition weak_saturation_number (G H : sgraph) (m : nat) : Prop :=
  (exists F : {set {set G}}, weakly_saturated H F /\ #|F| = m) /\
  (forall F : {set {set G}}, weakly_saturated H F -> m <= #|F|).

(** ** Statement *)

Definition proxy_OPG_weak_saturation_cube_in_clique : Prop :=
  exists p q N : nat, 0 < p /\
    forall n m : nat, N <= n ->
      weak_saturation_number 'K_n (hypercube 3) m ->
      weak_saturation_number 'K_(n + p) (hypercube 3) (m + q).
