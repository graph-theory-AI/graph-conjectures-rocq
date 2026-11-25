(** * Triangle-free strongly regular graphs

Godsil, "Problems in Algebraic Combinatorics", Electronic Journal of Combinatorics 2 (1995), F1;
Open Problem Garden, triangle_free_strongly_regular_graphs.

A k-regular graph on n vertices is strongly regular, with parameters (n,k,λ,μ), if any two
adjacent vertices have exactly λ common neighbours and any two distinct nonadjacent vertices
have exactly μ common neighbours; μ >= 1 is assumed, to eliminate degenerate graphs.  Seven
triangle-free strongly regular graphs are known: the 5-cycle, the Petersen graph, the Clebsch
graph, the Hoffman-Singleton graph, the Gewirtz graph, the M22 graph (with parameters
(77,16,0,4)) and the Higman-Sims graph.

Problem: is there an eighth triangle-free strongly regular graph?

The proposition states the positive answer: some nonempty triangle-free strongly regular graph
with 0 < μ < k is isomorphic to none of these seven graphs.

Encoding.  The condition μ < k is implicit in the source: it excludes the complete bipartite
graphs K_{k,k} (for which μ = k), which are not counted among the known graphs.  The empty graph,
which has all parameters, is excluded too.  The seven graphs are given by explicit adjacency
relations on {0,...,n-1}, or on binary words for the Clebsch graph. *)

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

(** The common neighbours of [u] and [v]. *)
Definition common_neigh (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** Every vertex has degree [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** [G] is strongly regular with parameters [k], [lam] and [mu] (complete and edgeless graphs
    are not excluded). *)
Definition strongly_regular (G : sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_neigh x y| = lam)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_neigh x y| = mu)].

(** [G] has no triangle. *)
Definition triangle_free (G : sgraph) : Prop :=
  forall x y z : G, x -- y -> y -- z -> z -- x -> False.

(** The cycle on [n] vertices ([3 <= n] is meant). *)
Definition cycle_graph (n : nat) : sgraph :=
  sgraph_of_rel (fun i j : 'I_n => (val i).+1 %% n == val j).

(** The Petersen graph: the edges are those of the outer 5-cycle, the spokes and those of the
    inner pentagram. *)
Definition petersen_graph : sgraph :=
  edge_list_graph 10
    [:: (0,1); (1,2); (2,3); (3,4); (4,0);
        (0,5); (1,6); (2,7); (3,8); (4,9);
        (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.

(** ** Definitions copied from GraphLib/spectral.v *)

(** The Clebsch graph (the folded 5-cube), with parameters (16,5,0,2): binary words of length 4 at
    distance 1 or 4 are adjacent. *)
Definition clebsch_graph : sgraph :=
  sgraph_of_rel (fun x y : 4.-tuple bool => #|[set i | tnth x i != tnth y i]| \in [:: 1; 4]).

(** Robertson's pentagons and pentagrams: the vertex [25 t + 5 h + j] is the [j]-th vertex of
    the [h]-th pentagon ([t = 0]) or pentagram ([t = 1]). *)
Definition hoffman_singleton_rel (a b : nat) : bool :=
  let ta := a %/ 25 in let ha := (a %% 25) %/ 5 in let ja := a %% 5 in
  let tb := b %/ 25 in let hb := (b %% 25) %/ 5 in let jb := b %% 5 in
  [|| [&& ta == 0, tb == 0, ha == hb & jb == (ja + 1) %% 5],
      [&& ta == 1, tb == 1, ha == hb & jb == (ja + 2) %% 5]
    | [&& ta == 0, tb == 1 & jb == (ha * hb + ja) %% 5]].

(** The Hoffman-Singleton graph, with parameters (50,7,0,1). *)
Definition hoffman_singleton_graph : sgraph :=
  sgraph_of_rel (fun x y : 'I_50 => hoffman_singleton_rel x y).

(** The 77 hexads of the Steiner system S(3,6,22) on [0, ..., 21], in lexicographic order. *)
Definition steiner_3_6_22 : seq (seq nat) :=
  [:: [:: 0; 1; 2; 4; 13; 16];
      [:: 0; 1; 3; 12; 15; 21];
      [:: 0; 1; 5; 6; 18; 20];
      [:: 0; 1; 7; 10; 11; 17];
      [:: 0; 1; 8; 9; 14; 19];
      [:: 0; 2; 3; 10; 18; 19];
      [:: 0; 2; 5; 7; 9; 12];
      [:: 0; 2; 6; 8; 15; 17];
      [:: 0; 2; 11; 14; 20; 21];
      [:: 0; 3; 4; 6; 7; 14];
      [:: 0; 3; 5; 8; 11; 16];
      [:: 0; 3; 9; 13; 17; 20];
      [:: 0; 4; 5; 17; 19; 21];
      [:: 0; 4; 8; 10; 12; 20];
      [:: 0; 4; 9; 11; 15; 18];
      [:: 0; 5; 10; 13; 14; 15];
      [:: 0; 6; 9; 10; 16; 21];
      [:: 0; 6; 11; 12; 13; 19];
      [:: 0; 7; 8; 13; 18; 21];
      [:: 0; 7; 15; 16; 19; 20];
      [:: 0; 12; 14; 16; 17; 18];
      [:: 1; 2; 3; 7; 8; 20];
      [:: 1; 2; 5; 11; 15; 19];
      [:: 1; 2; 6; 10; 12; 14];
      [:: 1; 2; 9; 17; 18; 21];
      [:: 1; 3; 4; 5; 9; 10];
      [:: 1; 3; 6; 16; 17; 19];
      [:: 1; 3; 11; 13; 14; 18];
      [:: 1; 4; 6; 8; 11; 21];
      [:: 1; 4; 7; 12; 18; 19];
      [:: 1; 4; 14; 15; 17; 20];
      [:: 1; 5; 7; 14; 16; 21];
      [:: 1; 5; 8; 12; 13; 17];
      [:: 1; 6; 7; 9; 13; 15];
      [:: 1; 8; 10; 15; 16; 18];
      [:: 1; 9; 11; 12; 16; 20];
      [:: 1; 10; 13; 19; 20; 21];
      [:: 2; 3; 4; 11; 12; 17];
      [:: 2; 3; 5; 6; 13; 21];
      [:: 2; 3; 9; 14; 15; 16];
      [:: 2; 4; 5; 8; 14; 18];
      [:: 2; 4; 6; 9; 19; 20];
      [:: 2; 4; 7; 10; 15; 21];
      [:: 2; 5; 10; 16; 17; 20];
      [:: 2; 6; 7; 11; 16; 18];
      [:: 2; 7; 13; 14; 17; 19];
      [:: 2; 8; 9; 10; 11; 13];
      [:: 2; 8; 12; 16; 19; 21];
      [:: 2; 12; 13; 15; 18; 20];
      [:: 3; 4; 8; 13; 15; 19];
      [:: 3; 4; 16; 18; 20; 21];
      [:: 3; 5; 7; 15; 17; 18];
      [:: 3; 5; 12; 14; 19; 20];
      [:: 3; 6; 8; 9; 12; 18];
      [:: 3; 6; 10; 11; 15; 20];
      [:: 3; 7; 9; 11; 19; 21];
      [:: 3; 7; 10; 12; 13; 16];
      [:: 3; 8; 10; 14; 17; 21];
      [:: 4; 5; 6; 12; 15; 16];
      [:: 4; 5; 7; 11; 13; 20];
      [:: 4; 6; 10; 13; 17; 18];
      [:: 4; 7; 8; 9; 16; 17];
      [:: 4; 9; 12; 13; 14; 21];
      [:: 4; 10; 11; 14; 16; 19];
      [:: 5; 6; 7; 8; 10; 19];
      [:: 5; 6; 9; 11; 14; 17];
      [:: 5; 8; 9; 15; 20; 21];
      [:: 5; 9; 13; 16; 18; 19];
      [:: 5; 10; 11; 12; 18; 21];
      [:: 6; 7; 12; 17; 20; 21];
      [:: 6; 8; 13; 14; 16; 20];
      [:: 6; 14; 15; 18; 19; 21];
      [:: 7; 8; 11; 12; 14; 15];
      [:: 7; 9; 10; 14; 18; 20];
      [:: 8; 11; 17; 18; 19; 20];
      [:: 9; 10; 12; 15; 17; 19];
      [:: 11; 13; 15; 16; 17; 21]].

(** The [i]-th hexad. *)
Definition hexad (i : nat) : seq nat := nth [::] steiner_3_6_22 i.

(** The [i]-th and [j]-th hexads are disjoint. *)
Definition hexads_disjoint (i j : nat) : bool := ~~ has (mem (hexad j)) (hexad i).

(** The M22 graph, with parameters (77,16,0,4): disjoint hexads are adjacent. *)
Definition m22_graph : sgraph := sgraph_of_rel (fun x y : 'I_77 => hexads_disjoint x y).

(** The Gewirtz graph, with parameters (56,10,0,2): disjoint hexads that avoid the point 0 are
    adjacent (the hexads through 0 are the first 21 ones). *)
Definition gewirtz_graph : sgraph :=
  sgraph_of_rel (fun x y : 'I_56 => hexads_disjoint (x + 21) (y + 21)).

(** The vertex 0 is joined to the points (1, ..., 22), a point to the hexads (23, ..., 99) that
    contain it, and two hexads are joined if they are disjoint. *)
Definition higman_sims_rel (a b : nat) : bool :=
  [|| (a == 0) && (1 <= b <= 22),
      [&& 1 <= a <= 22, 23 <= b & a.-1 \in hexad (b - 23)]
    | [&& 23 <= a, 23 <= b & hexads_disjoint (a - 23) (b - 23)]].

(** The Higman-Sims graph, with parameters (100,22,0,6). *)
Definition higman_sims_graph : sgraph := sgraph_of_rel (fun x y : 'I_100 => higman_sims_rel x y).

(** ** Definitions specific to the conjecture *)

(** The seven known triangle-free strongly regular graphs. *)
Definition known_triangle_free_srg (i : 'I_7) : sgraph :=
  match val i with
  | 0 => cycle_graph 5
  | 1 => petersen_graph
  | 2 => clebsch_graph
  | 3 => hoffman_singleton_graph
  | 4 => gewirtz_graph
  | 5 => m22_graph
  | _ => higman_sims_graph
  end.

(** ** Statement *)

Definition OPG_strongly_regular_triangle_free_eighth : Prop :=
  exists (G : sgraph) (k lam mu : nat),
    [/\ 0 < #|G|, triangle_free G, strongly_regular G k lam mu, 0 < mu & mu < k] /\
    forall i : 'I_7, ~ inhabited (G ≃ known_triangle_free_srg i).
