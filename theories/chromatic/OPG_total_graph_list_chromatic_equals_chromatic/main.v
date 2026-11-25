(** * The list total colouring conjecture

Borodin, Kostochka, Woodall, "List edge and list total colourings of multigraphs", J. Combin. Theory
Ser. B 71 (1997); Open Problem Garden, list_total_colouring_conjecture.

The total graph T(H) of a multigraph H has vertex set V(H) ∪ E(H).  Two vertices of H are adjacent
in T(H) if they are adjacent in H, two edges of H are adjacent in T(H) if they have a common end,
and a vertex of H is adjacent in T(H) to the edges of H incident to it.  The list chromatic number
χ_l(G) is the minimum k such that G has a proper colouring from all lists of at least k colours on
its vertices.

Conjecture: if G is the total graph of a multigraph, then χ_l(G) = χ(G).

Encoding.  Multigraphs are finite and may have parallel edges and loops.  "χ_l(G) = m" is a relation
between G and m. *)

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

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

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

(** ** Statement *)

Definition OPG_total_graph_list_chromatic_equals_chromatic : Prop :=
  forall (H : mgraph) (m : nat),
    choice_number (mtotal_graph H) m ->
    m = χ([set: mtotal_graph H]).
