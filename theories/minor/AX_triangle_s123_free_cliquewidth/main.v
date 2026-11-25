(** * Clique-width of (triangle, S_{1,2,3})-free graphs

Pilipczuk, Sintiari, Thomassé, Trotignon, "(Theta, triangle)-free and (even hole, K_4)-free
graphs. Part 2: bounds on treewidth", arXiv:2001.01607, open question (2001.01607__02).

S_{1,2,3} is the tree obtained from a vertex v by attaching three paths with 1, 2 and 3 edges.
A graph is (triangle, S_{1,2,3})-free if it has no induced subgraph isomorphic to one of them.
The clique-width of G is the minimum number of labels needed to build G by the following
operations: creation of a vertex with some label, disjoint union, addition of all the edges
between the vertices of label i and those of label j, for i <> j, and renaming of the label i
into j.

Question: do (triangle, S_{1,2,3})-free graphs have bounded clique-width?  The positive answer is
stated.

Encoding.  The constructions are expressions ([clique_width_expr]), whose leaves from left to right
are the vertices of the graph.  Graphs are required to be nonempty, as there is no expression for
the empty graph. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Lemma sgraph_of_rel_sym (V : finType) (r : rel V) :
  symmetric (fun x y => (x != y) && sc r x y).
Proof. by move=> x y /=; rewrite eq_sym orbC. Qed.

Lemma sgraph_of_rel_irrefl (V : finType) (r : rel V) :
  irreflexive (fun x y => (x != y) && sc r x y).
Proof. by move=> x; rewrite eqxx. Qed.

(** The graph on [V] whose edges are given by [r], up to symmetry and loops. *)
Definition sgraph_of_rel (V : finType) (r : rel V) : sgraph :=
  SGraph (@sgraph_of_rel_sym V r) (@sgraph_of_rel_irrefl V r).

(** The graph on [0, ..., n-1] whose edges are listed in [es]. *)
Definition edge_list_graph (n : nat) (es : seq (nat * nat)) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i, val j) \in es).

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** [G] has an induced subgraph isomorphic to [H]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

(** ** Definitions copied from GraphLib/minor.v *)

(** Expressions for labelled graphs: one vertex, disjoint union, all edges between two labels,
    relabelling. *)
Inductive clique_width_expr : Type :=
| CwLeaf of nat
| CwUnion of clique_width_expr & clique_width_expr
| CwJoin of nat & nat & clique_width_expr
| CwRelab of nat & nat & clique_width_expr.

(** The labels of the vertices, which are the leaves of the expression from left to right. *)
Fixpoint cw_labels (e : clique_width_expr) : seq nat :=
  match e with
  | CwLeaf i => [:: i]
  | CwUnion a b => cw_labels a ++ cw_labels b
  | CwJoin _ _ a => cw_labels a
  | CwRelab i j a => [seq (if l == i then j else l) | l <- cw_labels a]
  end.

(** The edges of the graph of the expression. *)
Fixpoint cw_edge (e : clique_width_expr) (x y : nat) : bool :=
  match e with
  | CwLeaf _ => false
  | CwUnion a b =>
      let n := size (cw_labels a) in
      if (x < n) && (y < n) then cw_edge a x y
      else if (n <= x) && (n <= y) then cw_edge b (x - n) (y - n)
      else false
  | CwJoin i j a =>
      let L := cw_labels a in
      cw_edge a x y ||
      [&& x != y, x < size L, y < size L &
          ((nth 0 L x == i) && (nth 0 L y == j)) ||
          ((nth 0 L x == j) && (nth 0 L y == i))]
  | CwRelab _ _ a => cw_edge a x y
  end.

(** The expression uses labels less than [k]. *)
Fixpoint cw_well_formed (k : nat) (e : clique_width_expr) : bool :=
  match e with
  | CwLeaf i => i < k
  | CwUnion a b => cw_well_formed k a && cw_well_formed k b
  | CwJoin i j a => [&& i < k, j < k, i != j & cw_well_formed k a]
  | CwRelab i j a => [&& i < k, j < k & cw_well_formed k a]
  end.

(** [G] is the graph of the expression [e]. *)
Definition cw_realizes (e : clique_width_expr) (G : sgraph) : Prop :=
  exists f : G -> nat,
    [/\ injective f,
        forall v : G, f v < size (cw_labels e),
        forall i : nat, i < size (cw_labels e) -> exists v : G, f v = i &
        forall u v : G, (u -- v) = cw_edge e (f u) (f v)].

(** The clique-width of [G] is at most [k] ([G] is nonempty). *)
Definition clique_width_le (G : sgraph) (k : nat) : Prop :=
  exists e : clique_width_expr, cw_well_formed k e /\ cw_realizes e G.

(** ** Definitions specific to the conjecture *)

(** S_{1,2,3}: the paths attached to 0 are 1, then 2 3, then 4 5 6. *)
Definition S123 : sgraph :=
  edge_list_graph 7 [:: (0,1); (0,2); (2,3); (0,4); (4,5); (5,6)].

(** ** Statement *)

Definition AX_triangle_s123_free_cliquewidth : Prop :=
  exists k : nat,
    forall G : sgraph,
      0 < #|G| -> triangle_free G -> ~ has_induced_copy G S123 ->
      clique_width_le G k.
