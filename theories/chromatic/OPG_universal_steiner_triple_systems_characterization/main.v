(** * Universal Steiner triple systems

Grannell, Griggs, Knor, Škoviera, "A Steiner triple system which colours all cubic graphs",
J. Graph Theory 46 (2004); Open Problem Garden, universal_steiner_triple_systems.

A Steiner triple system S consists of points and of triples of points, such that any two points
are in exactly one triple.  A cubic graph G is S-edge-colourable if its edges can be coloured by
the points of S so that the points assigned to the three edges around each vertex form a triple of
S.  S is universal if every simple cubic graph is S-edge-colourable.

S is projective if its points are the nonzero vectors of a vector space over F_2, and affine if
they are the vectors of a vector space over F_3; in both cases the triples are those of distinct
points whose sum is 0.  S is point-transitive if its automorphisms act transitively on its points.

Problem: which Steiner triple systems are universal?

The proposition states the answer for point-transitive systems: a point-transitive Steiner triple
system is universal if and only if it is neither projective nor affine (Holroyd, Škoviera; Král',
Máčajová, Pór, Sereni).  It is weaker than an answer to the problem, as it says nothing of the
systems that are not point-transitive.

Encoding.  A Steiner triple system is given by the set B of its triples, or blocks, on a finite type
of points.  Systems with at most three points, which are not universal, need no special treatment:
they are projective (including the empty system, for the null space).  Graphs are the finite
multigraphs of GraphTheory, with the hypothesis that there are no loops and no parallel edges. *)

From GraphTheory Require Import mgraph.
From mathcomp Require Import boot algebra perm.

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

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [G] has no loop and no parallel edges. *)
Definition msimple (G : mgraph) : Prop :=
  mloopless G /\ injective (fun e : edge G => [set source e; target e]).

(** The set [B] of blocks, on the set [T] of points, is a Steiner triple system: its blocks have
    three points, and two points are in exactly one block. *)
Definition steiner_triple_system (T : finType) (B : {set {set T}}) : Prop :=
  hg_uniform B 3 /\
  forall p q : T, p != q ->
    exists b : {set T},
      [/\ b \in B, p \in b, q \in b
        & forall b' : {set T}, b' \in B -> p \in b' -> q \in b' -> b' = b].

(** [G] is edge-colourable by the Steiner triple system [B]: the edges receive points such that
    the set of those around each vertex is a block ([G] is cubic and loopless). *)
Definition steiner_edge_colorable (G : mgraph) (T : finType) (B : {set {set T}}) : Prop :=
  exists c : edge G -> T, forall v : G, [set c e | e in edges_at v] \in B.

(** ** Definitions specific to the conjecture *)

(** [B] is universal: every simple cubic graph is edge-colourable by [B]. *)
Definition is_universal_sts (T : finType) (B : {set {set T}}) : Prop :=
  forall G : mgraph, msimple G -> mcubic G -> steiner_edge_colorable G B.

(** The map [f] sends the blocks to the triples of vectors of sum 0. *)
Definition zero_sum_blocks (p n : nat) (T : finType) (B : {set {set T}}) (f : T -> 'rV['F_p]_n) :
    Prop :=
  forall x y z : T, uniq [:: x; y; z] -> ([set x; y; z] \in B) = (f x + f y + f z == 0)%R.

(** The Steiner triple system [B] is projective: its points are the nonzero vectors of F_2^n. *)
Definition projective_sts (T : finType) (B : {set {set T}}) : Prop :=
  exists (n : nat) (f : T -> 'rV['F_2]_n),
    [/\ injective f, f @: [set: T] = [set v | v != 0%R] & zero_sum_blocks B f].

(** The Steiner triple system [B] is affine: its points are the vectors of F_3^n. *)
Definition affine_sts (T : finType) (B : {set {set T}}) : Prop :=
  exists (n : nat) (f : T -> 'rV['F_3]_n), bijective f /\ zero_sum_blocks B f.

(** The automorphisms of the set [B] of blocks act transitively on the points. *)
Definition point_transitive_sts (T : finType) (B : {set {set T}}) : Prop :=
  forall x y : T,
    exists s : {perm T}, s x = y /\ forall b : {set T}, b \in B -> s @: b \in B.

(** ** Statement *)

(** A point-transitive Steiner triple system is universal if and only if it is neither projective
    nor affine. *)
Definition proxy_OPG_universal_steiner_triple_systems_characterization : Prop :=
  forall (T : finType) (B : {set {set T}}),
    steiner_triple_system B -> point_transitive_sts B ->
    (is_universal_sts B <-> ~ projective_sts B /\ ~ affine_sts B).
