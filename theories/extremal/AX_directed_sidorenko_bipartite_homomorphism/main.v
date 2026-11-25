(** * Directed Sidorenko conjecture

Fox, Himwich, Mani, Zhou, "A note on directed analogues of the Sidorenko and forcing conjectures",
arXiv:2210.16971, Conjecture 1.4 (2210.16971__00).

The homomorphism density t(B,D) of a digraph B in a digraph D is the fraction of the maps from
V(B) to V(D) that are homomorphisms.  Let K be the digraph with two vertices and one arc.  An
oriented graph B has the directed Sidorenko property if t(B,D) >= t(K,D)^e(B) for every oriented
graph D, where e(B) is the number of arcs of B.

Conjecture 1.4: if B is a bipartite oriented graph with a homomorphism to K, then B has the
directed Sidorenko property.

Encoding.  Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
relation [--].  Oriented graphs are those without digon (nor loop).  The inequality between
densities is multiplied by |V(D)|^|V(B)| |V(D)|^(2e(B)).  It is thus true when D is empty.  That B
is bipartite follows from the homomorphism to K. *)

From GraphTheory Require Import digraph connectivity.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [G] is bipartite: it has a bipartition (a set [A] such that each edge has exactly one end in
    [A]). *)
Definition bipartite (G : diGraph) : Prop := exists A : {set G}, bipartition A.

(** ** Definitions copied from GraphLib/homomorphism.v *)

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** ** Definitions copied from GraphLib/digraph.v *)

(** [D] is oriented: it has no digon, and no loop. *)
Definition oriented (D : diGraph) : Prop :=
  forall x y : D, x -- y -> ~~ (y -- x).

(** ** Definitions copied from GraphLib/extremal.v *)

(** [B] is Sidorenko among oriented graphs: the density of homomorphisms from
    [B] to any oriented graph is at least the power [num_edges B] of its density. *)
Definition directed_sidorenko (B : diGraph) : Prop :=
  forall D : diGraph,
    oriented D ->
    num_edges D ^ num_edges B * #|D| ^ #|B|
      <= hom_count B D * #|D| ^ (2 * num_edges B).

(** ** Definitions specific to the conjecture *)

(** The digraph with two vertices ([false] and [true]) and one arc, from [false] to [true]. *)
Definition single_arc : diGraph := DiGraph [rel x y : bool | ~~ x && y].

(** ** Statement *)

Definition AX_directed_sidorenko_bipartite_homomorphism : Prop :=
  forall B : diGraph,
    oriented B ->
    bipartite B ->
    homs_to B single_arc ->
    directed_sidorenko B.
