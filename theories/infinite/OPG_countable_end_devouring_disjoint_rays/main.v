(** * End-devouring rays

Georgakopoulos, "Infinite Hamilton cycles in squares of locally finite graphs"; Open Problem
Garden, end_devouring_rays.

A ray is a one-way infinite path, and an end is a class of rays, two rays being equivalent if no
finite set of vertices separates their tails.  The rays of an end ω are called ω-rays.  A set of
rays devours the end ω if every ω-ray meets some ray of this set.  An end is countable if some
countable set of rays devours it.

Conjecture: let G be a graph, ω a countable end of G, and K an infinite set of pairwise disjoint
ω-rays in G.  Then there is a set K' of pairwise disjoint ω-rays that devours ω such that the set
of starting vertices of the rays of K' equals the set of starting vertices of the rays of K.

Encoding.  Graphs are simple, with an arbitrary type of vertices and an adjacency relation in
[Prop].  A ray is an injective sequence of vertices, and the end ω is given by one of its rays.  The
countable set of rays that devours ω is a family of rays indexed by the natural numbers, possibly
with repetitions; these rays are not required to be in ω.  The infinite sets K and K' are families
of pairwise disjoint rays indexed by the natural numbers.  This is not a restriction: if a countable
set of vertices meets all ω-rays, then every set of pairwise disjoint ω-rays is countable, and the
rays of K' correspond to their starting vertices, which are those of the rays of K. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/infinite.v *)

(** Simple graphs, possibly infinite. *)
Record iGraph := Build_iGraph {
  ivertex : Type;
  iedge : ivertex -> ivertex -> Prop;
  iedge_sym : forall x y, iedge x y -> iedge y x;
  iedge_irrefl : forall x, ~ iedge x x }.

(** The set [P] is finite. *)
Definition ifinite_set (T : Type) (P : T -> Prop) : Prop :=
  exists (n : nat) (g : 'I_n -> T), forall x, P x -> exists i : 'I_n, g i = x.

(** There is a walk with vertices in [P]. *)
Inductive ireach (G : iGraph) (P : ivertex G -> Prop) : ivertex G -> ivertex G -> Prop :=
  | ireach0 x : P x -> ireach P x x
  | ireachS x y z : ireach P x y -> iedge y z -> P z -> ireach P x z.

(** [r] is a ray: a one-way infinite path. *)
Definition ray (G : iGraph) (r : nat -> ivertex G) : Prop :=
  injective r /\ forall n, iedge (r n) (r n.+1).

(** The rays [r] and [r'] are in the same end: for each finite set [S], they have tails in the
    same component of the complement of [S]. *)
Definition end_equiv (G : iGraph) (r r' : nat -> ivertex G) : Prop :=
  forall S : ivertex G -> Prop, ifinite_set S ->
    exists N : nat, forall n : nat, N <= n ->
      exists m : nat, N <= m /\ ireach (fun v => ~ S v) (r n) (r' m).

(** ** Definitions specific to the conjecture *)

(** [r] is a ray of the end of the ray [w]. *)
Definition ray_of_end (G : iGraph) (w r : nat -> ivertex G) : Prop :=
  ray r /\ end_equiv r w.

(** The sequences [K i] are pairwise disjoint. *)
Definition disjoint_rays (G : iGraph) (K : nat -> nat -> ivertex G) : Prop :=
  forall i j n m, i <> j -> K i n <> K j m.

(** The rays [K i] devour the end of the ray [w]: they meet all rays of this end. *)
Definition devours (G : iGraph) (w : nat -> ivertex G) (K : nat -> nat -> ivertex G) : Prop :=
  forall r : nat -> ivertex G, ray_of_end w r -> exists i n m, r n = K i m.

(** The end of the ray [w] is countable: countably many rays devour it. *)
Definition countable_end (G : iGraph) (w : nat -> ivertex G) : Prop :=
  exists K : nat -> nat -> ivertex G, (forall i, ray (K i)) /\ devours w K.

(** The sequences [K i] and [K' i] have the same starting vertices. *)
Definition same_starts (G : iGraph) (K K' : nat -> nat -> ivertex G) : Prop :=
  (forall i, exists j, K' j 0 = K i 0) /\ (forall j, exists i, K i 0 = K' j 0).

(** ** Statement *)

Definition OPG_countable_end_devouring_disjoint_rays : Prop :=
  forall (G : iGraph) (w : nat -> ivertex G) (K : nat -> nat -> ivertex G),
    ray w -> countable_end w ->
    (forall i, ray_of_end w (K i)) -> disjoint_rays K ->
    exists K' : nat -> nat -> ivertex G,
      [/\ forall i, ray_of_end w (K' i), disjoint_rays K', devours w K' & same_starts K K'].
