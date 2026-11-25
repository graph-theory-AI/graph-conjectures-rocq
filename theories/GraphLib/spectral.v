(** * Spectra, strongly regular graphs

    Matrices of simple graphs, spectra, and some strongly regular graphs.  The vertices of [G]
    are numbered by [enum_val]. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot order algebra fingroup perm.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Matrices *)

Section Matrices.
Variable R : nzRingType.

(** The adjacency matrix of [G]. *)
Definition adjacency_mx (G : sgraph) : 'M[R]_(#|G|) :=
  \matrix_(i, j) (if enum_val i -- enum_val j then 1 else 0).

(** The diagonal matrix of the degrees. *)
Definition degree_mx (G : sgraph) : 'M[R]_(#|G|) :=
  diag_mx (\row_i #|N(enum_val i)|%:R).

(** The Laplacian matrix of [G]. *)
Definition laplacian_mx (G : sgraph) : 'M[R]_(#|G|) := degree_mx G - adjacency_mx G.

End Matrices.

Section RealSpectrum.
Variable R : rcfType.

(** All eigenvalues of [A] have absolute value at most [b] (real eigenvalues only: [A] is meant
    to be symmetric). *)
Definition spectral_radius_le (n : nat) (A : 'M[R]_n) (b : R) : Prop :=
  forall x : R, eigenvalue A x -> `|x| <= b.

(** [S] is a signing of the adjacency matrix of [G]: a symmetric matrix obtained by replacing
    some entries [1] by [-1]. *)
Definition is_signing (G : sgraph) (S : 'M[R]_(#|G|)) : Prop :=
  (forall i j, S i j = S j i) /\
  (forall i j, if enum_val i -- enum_val j
               then (S i j = 1) \/ (S i j = -1)
               else S i j = 0).

(** [s] is the list of the eigenvalues of [A] with multiplicities, in nonincreasing order. *)
Definition is_spectrum (n : nat) (A : 'M[R]_n) (s : seq R) : Prop :=
  [/\ size s = n, sorted (fun x y : R => y <= x) s
    & char_poly A = \prod_(x <- s) ('X - x%:P)].

End RealSpectrum.

(** ** Cospectral graphs *)

(** [G] and [H] are cospectral: their adjacency matrices have the same spectrum, with
    multiplicities. *)
Definition cospectral (G H : sgraph) : bool :=
  char_poly (adjacency_mx int G) == char_poly (adjacency_mx int H).

(** The graph on [0, ..., n-1] with edge set [E] is determined by its spectrum: the graphs on
    [0, ..., n-1] cospectral with it are isomorphic to it. *)
Definition spectrum_determined (n : nat) (E : {set {set 'I_n}}) : bool :=
  [forall F : {set {set 'I_n}},
     (F \subset E('K_n)) ==> cospectral (sgraph_of_edges E) (sgraph_of_edges F) ==>
     [exists s : 'S_n, F == [set s @: e | e : {set 'I_n} in E]]].

Local Close Scope ring_scope.

(** ** Some triangle-free strongly regular graphs *)

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
