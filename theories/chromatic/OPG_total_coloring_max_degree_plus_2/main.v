(** * The total colouring conjecture

Behzad, "Graphs and their chromatic numbers", Ph.D. thesis, Michigan State University, 1965;
Open Problem Garden, behzads_conjecture.

A total colouring of a graph G is an assignment of colours to the vertices and the edges of G such
that any two adjacent vertices, any two edges with a common end, and any vertex and incident edge
receive different colours.  The total chromatic number χ''(G) is the minimum number of colours of a
total colouring of G.

Conjecture: χ''(G) is Δ(G) + 1 or Δ(G) + 2 for every graph G of maximum degree Δ(G).

Encoding.  Graphs are the finite multigraphs of GraphTheory, with the hypothesis that there are no
loops and no parallel edges.  The total colourings of G are the vertex colourings of its total
graph.  The empty graph is excluded, as its total chromatic number is 0. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import digraph sgraph coloring.
From GraphTheory Require skeleton.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** Multigraphs without labels. *)
Abbreviation mgraph := (graph unit unit).

(** [G] has no loop. *)
Definition mloopless (G : mgraph) : Prop := forall e : edge G, source e != target e.

(** The maximum number of edges incident to a vertex (a loop is counted once). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

(** Distinct edges with a common end. *)
Definition mline_rel (G : mgraph) : rel (edge G) :=
  fun e1 e2 => (e1 != e2) && [exists v : G, incident v e1 && incident v e2].

Lemma mline_rel_sym (G : mgraph) : symmetric (@mline_rel G).
Proof.
move=> e1 e2; rewrite /mline_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[v Hv]; exists v; rewrite andbC.
Qed.

Lemma mline_rel_irrefl (G : mgraph) : irreflexive (@mline_rel G).
Proof. by move=> e; rewrite /mline_rel eqxx. Qed.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The edges of the total graph of a multigraph ([sk_rel]: distinct and adjacent vertices). *)
Definition mtotal_rel (G : mgraph) : rel (G + edge G)%type :=
  fun a b =>
    match a, b with
    | inl x, inl y => skeleton.sk_rel x y
    | inr e, inr f => @mline_rel G e f
    | inl x, inr e => incident x e
    | inr e, inl x => incident x e
    end.

Lemma mtotal_rel_sym (G : mgraph) : symmetric (@mtotal_rel G).
Proof.
move=> [x|e] [y|f] //=.
- by rewrite skeleton.sk_rel_sym.
- by rewrite mline_rel_sym.
Qed.

Lemma mtotal_rel_irrefl (G : mgraph) : irreflexive (@mtotal_rel G).
Proof. by move=> [x|e] /=; [rewrite skeleton.sk_rel_irrefl | rewrite mline_rel_irrefl]. Qed.

(** The total graph of the multigraph [G]. *)
Definition mtotal_graph (G : mgraph) : sgraph :=
  SGraph (@mtotal_rel_sym G) (@mtotal_rel_irrefl G).

(** The total chromatic number of [G]. *)
Definition mtotal_chromatic_number (G : mgraph) : nat := χ([set: mtotal_graph G]).

(** [G] has no loop and no parallel edges. *)
Definition msimple (G : mgraph) : Prop :=
  mloopless G /\ injective (fun e : edge G => [set source e; target e]).

(** ** Statement *)

Definition OPG_total_coloring_max_degree_plus_2 : Prop :=
  forall G : mgraph, msimple G -> 0 < #|G| ->
    (mDelta G).+1 <= mtotal_chromatic_number G <= (mDelta G).+2.
