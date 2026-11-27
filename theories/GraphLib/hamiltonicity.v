(** * Hamiltonian paths and cycles

Paths and cycles are sequences of vertices.  A Hamiltonian cycle may have length at most 2: the
graphs with two adjacent vertices, as well as the empty graph, are Hamiltonian, and the graph
with one vertex is not. *)

From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [c] is a Hamiltonian cycle of [G]. *)
Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments hamiltonian_cycle : clear implicits.

(** [G] is Hamiltonian. *)
Definition hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, hamiltonian_cycle G c.

(** [s] is a Hamiltonian path of [G]. *)
Definition hamiltonian_path (G : sgraph) (s : seq G) : bool :=
  [&& sorted (--) s, uniq s & size s == #|G|].
Arguments hamiltonian_path : clear implicits.

(** [G] is traceable: it has a Hamiltonian path. *)
Definition traceable (G : sgraph) : Prop :=
  exists s : seq G, hamiltonian_path G s.

(** The set of the edge sets of the Hamiltonian cycles of [G]. *)
Definition hamiltonian_edge_sets (G : sgraph) : {set {set {set G}}} :=
  [set A : {set {set G}} |
    [exists c : (#|G|).-tuple G,
       hamiltonian_cycle G c && (A == seq_cycle_edge_set c)]].

(** [G] is uniquely Hamiltonian: it has exactly one Hamiltonian cycle, up to its edge set. *)
Definition uniquely_hamiltonian (G : sgraph) : Prop :=
  #|hamiltonian_edge_sets G| = 1.

(** [G] is [k]-tough: if the deletion of [S] leaves at least two components, there are at most
    [#|S| / k] of them. *)
Definition tough (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    1 < #|components (~: S)| -> k * #|components (~: S)| <= #|S|.

(** [G] is hypohamiltonian: it is not Hamiltonian, but it is after the deletion of any vertex. *)
Definition hypohamiltonian (G : sgraph) : Prop :=
  ~ hamiltonian G /\ forall v : G, hamiltonian (induced [set~ v]).

(** [G] is hypotraceable: it is not traceable, but it is after the deletion of any vertex. *)
Definition hypotraceable (G : sgraph) : Prop :=
  ~ traceable G /\ forall v : G, traceable (induced [set~ v]).

(** [w] is a TSP walk: a closed walk that visits all vertices. *)
Definition tsp_walk (G : sgraph) (w : seq G) : Prop :=
  exists x p,
    [/\ w = x :: p,
        path (--) x p,
        last x p = x
      & forall v : G, v \in w].

(** ** Claw-free graphs *)

(** Line graphs are claw-free: the three leaves of a claw would be pairwise disjoint edges, each
    meeting the edge at the centre, which has only two ends. *)
Lemma simple_line_graph_claw_free (G : sgraph) : claw_free (simple_line_graph G).
Proof.
move=> [h]; pose c := val (h (inl ord0)); pose l i := val (h (inr i)).
have /fin_all_exists[v vP] (i : 'I_3) : exists x, x \in l i :&: c.
  by apply/set0Pn; have := isubgraph_mono h (inr i) (inl ord0); case/andP.
have /card_imset vinj : injective v.
  move=> i j vij; apply/eqP/negPn/negP => ij.
  have := isubgraph_mono h (inr i) (inr j); rewrite /edge_rel /= /kb_rel /= => /negbT.
  rewrite negb_and negbK => /orP[/eqP/val_inj/(isubgraph_inj h)[/eqP]|].
    by rewrite (negbTE ij).
  case/set0Pn; exists (v i); move: (vP i) (vP j).
  by rewrite -vij !inE => /andP[-> _] /andP[->].
have : #|v @: [set: 'I_3]| <= #|c|.
  by apply/subset_leq_card/subsetP => _ /imsetP[i _ ->]; move: (vP i); rewrite inE => /andP[].
rewrite vinj cardsT card_ord /c; case/edgesP: (valP (h (inl ord0))) => x [y [-> _]].
by rewrite cards2; case: (x != y).
Qed.
