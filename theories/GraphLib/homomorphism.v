(** * Homomorphisms

    Homomorphisms are those of GraphTheory ([is_dhom]), between digraphs or simple graphs: a
    simple graph is seen as a digraph by a coercion. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.
From GC.GraphLib Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** There is a homomorphism from [G] to [H]. *)
Definition homs_to (G H : diGraph) : Prop := exists f : G -> H, is_dhom f.

(** [G] and [H] are homomorphically equivalent. *)
Definition hom_equiv (G H : diGraph) : Prop := homs_to G H /\ homs_to H G.

(** [G] is a core: all its endomorphisms are bijective. *)
Definition is_core (G : diGraph) : Prop := forall f : G -> G, is_dhom f -> bijective f.

(** The number of homomorphisms from [H] to [G] (of endomorphisms of [G] if [H] is [G]). *)
Definition hom_count (H G : diGraph) : nat :=
  #|[set f : {ffun H -> G} | [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]]|.

(** The [t]-th cartesian power of [G] ([K_1] for [t = 0]). *)
Fixpoint cartesian_power (G : sgraph) (t : nat) : sgraph :=
  if t is t'.+1 then cartesian_product (cartesian_power G t') G else 'K_1.
