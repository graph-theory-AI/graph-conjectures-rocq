(** * The 3-edge-colouring conjecture

Hoffmann-Ostenhof; Open Problem Garden, 3_edge_coloring_conjecture.

A graph is cubic if all its degrees are 3.  A 3-edge-colouring is a proper colouring of the edges
with 3 colours (distinct edges with a common end have different colours).  Two graphs are
homeomorphic if they have isomorphic subdivisions.  For an edge e of a cubic graph G, the cubic
graph homeomorphic to G - e is obtained from G - e by suppressing the two ends of e, which have
degree 2.

Conjecture: let G be a connected cubic graph with |V(G)| > 2 that has a 3-edge-colouring.  Then G
has an edge e such that the cubic graph homeomorphic to G - e has a 3-edge-colouring.

Encoding.  Graphs are finite multigraphs with parallel edges.  They have no loop, as a graph with a
loop has no 3-edge-colouring.  The cubic graph homeomorphic to G - e, unique up to isomorphism, is
any loopless cubic multigraph H homeomorphic to G - e.  (There is none if suppressing the ends of e
creates a loop: such an edge e does not satisfy the conclusion.) *)

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

(** Every vertex is incident to [r] edges (a loop is counted once). *)
Definition mregular (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

(** Every vertex is incident to three edges (a loop is counted once). *)
Definition mcubic (G : mgraph) : Prop := mregular G 3.

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

(** The line graph of the multigraph [G] (parallel edges are adjacent). *)
Definition mline_graph (G : mgraph) : sgraph := SGraph (@mline_rel_sym G) (@mline_rel_irrefl G).

(** [G] and [H] are isomorphic: there are bijections between their vertices and between their
    edges that preserve the incidence. *)
Definition misomorphic (G H : mgraph) : Prop :=
  exists (f : G -> H) (g : edge G -> edge H),
    [/\ bijective f, bijective g & forall x e, incident (f x) (g e) = incident x e].

(** [G] where the edge [e0] from [x] to [y] is replaced by a path [x z y], for a new vertex [z],
    which is [None]: [e0] becomes the edge [x z], and [None] is the new edge [z y]. *)
Definition msubdivide_edge (G : mgraph) (e0 : edge G) : mgraph :=
  @Graph unit unit (option G) (option (edge G))
    (fun b oe =>
       match oe with
       | Some e => if b && (e == e0) then None else Some (endpoint b e)
       | None => if b then Some (target e0) else None
       end)
    (fun=> tt) (fun=> tt).

(** [K] is a subdivision of [G], up to isomorphism: it is obtained by subdividing edges one by
    one. *)
Inductive msubdivision (G K : mgraph) : Prop :=
| msubdivision_iso of misomorphic G K
| msubdivision_step (e : edge G) of msubdivision (msubdivide_edge e) K.

(** [G] and [H] are homeomorphic: they have a common subdivision. *)
Definition mhomeomorphic (G H : mgraph) : Prop :=
  exists K : mgraph, msubdivision G K /\ msubdivision H K.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** The chromatic index of [G] ([0] for [G] without edges; loops are allowed). *)
Definition mchromatic_index (G : mgraph) : nat := χ([set: mline_graph G]).

(** ** Statement *)

Definition OPG_cubic_3_edge_colorable_edge_removal : Prop :=
  forall G : mgraph,
    mloopless G -> mcubic G -> connected [set: skeleton.skeleton G] -> 2 < #|G| ->
    mchromatic_index G <= 3 ->
    exists (e : edge G) (H : mgraph),
      [/\ mloopless H, mcubic H, mhomeomorphic (remove_edges [set e]) H
        & mchromatic_index H <= 3].
