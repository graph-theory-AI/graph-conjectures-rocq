(** * Vizing's interchange conjecture

Vizing; Bondy, Murty, "Graph Theory", Appendix A, problem 60.

Given a proper edge colouring of a graph G, the edges of two colours a and b form a graph whose
components are alternating paths and cycles.  An interchange (Kempe change) consists in exchanging
a and b on one of these components.  The chromatic index χ'(G) is the minimum number of colours of
a proper edge colouring of G.

Conjecture: given a proper edge colouring of a graph G, a proper edge colouring of G with χ'(G)
colours can be obtained by a sequence of interchanges.

Encoding.  Graphs are finite and simple.  The given colouring and the interchanges use colours in
{0, ..., k-1}, for any k.  An edge colouring is a map on the sets of vertices, whose values on the
sets that are not edges are irrelevant.  The chromatic index is the chromatic number of the line
graph.  The exchange is done on a union of components, which is a composition of interchanges. *)

From GraphTheory Require Import digraph sgraph coloring.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section SimpleLineGraph.
Variable G : sgraph.

(** The edges of [G]. *)
Definition simple_line_vertex : Type := {e : {set G} | e \in E(G)}.

(** Distinct edges with a common end. *)
Definition simple_line_rel : rel simple_line_vertex :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma simple_line_sym : symmetric simple_line_rel.
Proof. by move=> e f; rewrite /simple_line_rel eq_sym setIC. Qed.

Lemma simple_line_irrefl : irreflexive simple_line_rel.
Proof. by move=> e; rewrite /simple_line_rel eqxx. Qed.

(** The line graph of the simple graph [G]. *)
Definition simple_line_graph : sgraph := SGraph simple_line_sym simple_line_irrefl.

End SimpleLineGraph.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [col] is a proper edge colouring. *)
Definition proper_edge_coloring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

(** ** Definitions specific to the conjecture *)

(** The colours of the edges of [G]. *)
Definition used_colours (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : {set 'I_k} :=
  [set col e | e in E(G)].

(** [col'] is obtained from [col] by exchanging two colours [a] and [b] on a union [K] of
    components of the graph of the edges with these colours. *)
Definition kempe_step (G : sgraph) (k : nat) (col col' : {set G} -> 'I_k) : Prop :=
  exists (a b : 'I_k) (K : {set {set G}}),
    [/\ K \subset E(G),
        forall e : {set G}, e \in K -> (col e == a) || (col e == b),
        forall e f : {set G}, e \in K -> f \in E(G) -> e :&: f != set0 ->
          (col f == a) || (col f == b) -> f \in K &
        forall e : {set G},
          col' e = if e \in K then (if col e == a then b else a) else col e].

(** [col'] is obtained from [col] by at most [n] steps. *)
Fixpoint kempe_reach (G : sgraph) (k n : nat) (col col' : {set G} -> 'I_k) {struct n} : Prop :=
  match n with
  | 0 => col = col'
  | n'.+1 =>
      col = col' \/
      exists c : {set G} -> 'I_k, kempe_step col c /\ kempe_reach n' c col'
  end.

(** ** Statement *)

Definition BM_vizing_interchange_kempe_optimal_edge_coloring : Prop :=
  forall (G : sgraph) (k : nat) (col : {set G} -> 'I_k),
    proper_edge_coloring col ->
    exists (n : nat) (col' : {set G} -> 'I_k),
      [/\ kempe_reach n col col',
          proper_edge_coloring col' &
          #|used_colours col'| <= χ([set: simple_line_graph G])].
