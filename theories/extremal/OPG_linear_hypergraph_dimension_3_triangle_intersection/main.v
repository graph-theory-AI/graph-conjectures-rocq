(** * Linear hypergraphs with dimension 3

de Fraysseix, Ossona de Mendez, Rosenstiehl; Open Problem Garden,
linear_hypergraphs_with_dimension_3.

A hypergraph is linear if any two edges have at most one common vertex.  Its incidence poset is the
set of its vertices and edges, ordered by v < e if v ∈ e.  The dimension of a poset is the minimum
number of linear extensions whose intersection is this poset.  The intersection hypergraph of a
family of sets has these sets as vertices, and its edges are the maximal subfamilies of at least two
sets with a common point.

Conjecture: every linear hypergraph whose incidence poset has dimension at most 3 is the
intersection hypergraph of a family of triangles and segments in the plane.

Encoding.  Edges have at least two vertices, which is implicit: an edge with one vertex contained in
another edge is not a maximal subfamily.  The incidence poset is extended by the sets of vertices
that are not edges, as isolated elements; this does not change whether its dimension is at most 3.
Each vertex is represented by the convex hull of three points, which is a triangle, a segment or a
point.  Allowing points is not a restriction, as a point can be replaced by a small segment.  The
plane is R^2 for any real closed field R, which is equivalent to the case of the real numbers
(Tarski). *)

From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions copied from GraphLib/misc.v *)

(** [l] is a linear order. *)
Definition is_linear_order (X : finType) (l : rel X) : Prop :=
  [/\ reflexive l, antisymmetric l, transitive l & total l].

(** The list [ls] is a realizer of [le]: linear extensions whose intersection is [le]. *)
Definition realizer (X : finType) (le : rel X) (ls : seq (rel X)) : Prop :=
  (forall i : nat, i < size ls ->
     is_linear_order (nth (fun _ _ => false) ls i) /\
     subrel le (nth (fun _ _ => false) ls i)) /\
  (forall x y : X, le x y <->
     (forall i : nat, i < size ls -> (nth (fun _ _ => false) ls i) x y)).

(** The (Dushnik-Miller) dimension of the order [le] is at most [d]. *)
Definition poset_dim_le (X : finType) (le : rel X) (d : nat) : Prop :=
  exists ls : seq (rel X), size ls <= d /\ realizer le ls.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** Every edge has at least two vertices. *)
Definition hg_loopless E : Prop := forall e, e \in E -> 2 <= #|e|.

(** [E] is linear: distinct edges have at most one common vertex. *)
Definition hg_linear E : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e != f -> #|e :&: f| <= 1.

End Hypergraph.

(** ** Definitions copied from GraphLib/extremal.v *)

(** The incidence order of the hypergraph [E]: a vertex is below the edges that contain it (the
    sets that are not in [E] are isolated elements). *)
Definition incidence_order (T : finType) (E : {set {set T}}) : rel (T + {set T}) :=
  fun x y =>
    match x, y with
    | inl v, inl w => v == w
    | inl v, inr e => (e \in E) && (v \in e)
    | inr e, inr f => e == f
    | inr _, inl _ => false
    end.

(** ** Definitions specific to the conjecture *)

Section Triangles.
Local Open Scope ring_scope.
Variable R : rcfType.

(** The point [p] is in the triangle with corners [t 0], [t 1], [t 2] (which is a segment or a
    point if they are on a line). *)
Definition in_triangle (t : 'I_3 -> R * R) (p : R * R) : Prop :=
  exists l : 'I_3 -> R,
    [/\ forall i, 0 <= l i, \sum_i l i = 1,
        p.1 = \sum_i l i * (t i).1 & p.2 = \sum_i l i * (t i).2].

End Triangles.

(** The members of the family [obj] indexed by [S] have a common point. *)
Definition common_point (R : rcfType) (T : finType) (obj : T -> 'I_3 -> R * R) (S : {set T}) :
    Prop :=
  exists p : R * R, forall v : T, v \in S -> in_triangle (obj v) p.

(** [E] is the intersection hypergraph of the family [obj]: its edges are the maximal sets of at
    least two indices whose members have a common point. *)
Definition intersection_hypergraph (R : rcfType) (T : finType) (obj : T -> 'I_3 -> R * R)
    (E : {set {set T}}) : Prop :=
  forall S : {set T},
    S \in E <->
    [/\ 2 <= #|S|, common_point obj S
      & forall S' : {set T}, S \subset S' -> common_point obj S' -> S' = S].

(** ** Statement *)

Definition OPG_linear_hypergraph_dimension_3_triangle_intersection : Prop :=
  forall (R : rcfType) (T : finType) (E : {set {set T}}),
    hg_loopless E -> hg_linear E -> poset_dim_le (incidence_order E) 3 ->
    exists obj : T -> 'I_3 -> R * R, intersection_hypergraph obj E.
