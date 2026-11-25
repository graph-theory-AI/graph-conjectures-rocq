(** * Clustered coloring number of minor-closed classes

Dvořák, Norin, "Islands in minor-closed classes. I. Bounded treewidth and separators",
arXiv:1710.02727, Conjecture 4 (1710.02727__00).

A t-island in a graph G is a nonempty set S of vertices such that each vertex of S has fewer than t
neighbours outside S.  Let col_C(G) be the smallest t such that every nonempty subgraph of G
contains a t-island of size at most C.  For a class 𝒢 of graphs, col*(𝒢) is the smallest t such
that for some C, col_C(G) <= t for every graph G in 𝒢.  The graph I_{t-1} + P_m is obtained from a
path on m vertices by adding t-1 pairwise nonadjacent vertices, adjacent to all the vertices of the
path.

Conjecture 4: a minor-closed class 𝒢 satisfies col*(𝒢) <= t if and only if there exists m >= 1 such
that K_{t,m} and I_{t-1} + P_m are not in 𝒢.

Encoding.  Graphs are finite and simple, and a class is a predicate on graphs.  In the definition
of col_C, the subgraphs are the induced ones; this is equivalent, as a t-island of an induced
subgraph is a t-island of its spanning subgraphs.  "H is not in 𝒢" is replaced by "no graph of 𝒢
has H as a minor", which is equivalent for a minor-closed class.  The condition t >= 1 is implicit
in the source. *)

From GraphTheory Require Import preliminaries digraph sgraph minor.
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

(** ** Definitions specific to the conjecture *)

(** [S] is a [t]-island of [G]. *)
Definition t_island (G : sgraph) (S : {set G}) (t : nat) : Prop :=
  S != set0 /\
  forall v : G, v \in S -> #|N(v) :\: S| < t.

(** col*([C]) is at most [t]. *)
Definition col_star_le (C : sgraph -> Prop) (t : nat) : Prop :=
  exists c : nat,
    0 < c /\
    forall (G : sgraph) (A : {set G}),
      C G -> A != set0 ->
      exists S : {set induced A},
        #|S| <= c /\ t_island S t.

(** The edges of I_{[t]-1} + P_[m], where [inl _] are the vertices of I_{[t]-1} and [inr _] those
    of P_[m]. *)
Definition join_path_rel (t m : nat) : rel ('I_t.-1 + 'I_m) :=
  fun x y =>
    match x, y with
    | inl _, inl _ => false
    | inl _, inr _ | inr _, inl _ => true
    | inr i, inr j => ((val i).+1 == val j) || ((val j).+1 == val i)
    end.

(** The graph I_{[t]-1} + P_[m]. *)
Definition join_path (t m : nat) : sgraph :=
  @sgraph_of_rel ('I_t.-1 + 'I_m)%type (@join_path_rel t m).

(** [1 <= m], and no graph of [C] has K_{[t],[m]} or I_{[t]-1} + P_[m] as a minor. *)
Definition forbids_Ktm_and_join_path (C : sgraph -> Prop) (t m : nat) : Prop :=
  1 <= m /\
  forall G : sgraph,
    C G -> ~ minor G (KB t m) /\ ~ minor G (join_path t m).

(** ** Statement *)

Definition AX_minor_closed_col_star_characterization : Prop :=
  forall (C : sgraph -> Prop) (t : nat),
    1 <= t ->
    (forall G H : sgraph, C G -> minor G H -> C H) ->
    col_star_le C t <->
    exists m : nat, forbids_Ktm_and_join_path C t m.
