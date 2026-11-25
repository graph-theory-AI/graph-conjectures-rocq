(** * The list Hadwiger conjecture

Kawarabayashi and Mohar, "A relaxed Hadwiger's conjecture for list colorings", J. Combin. Theory
Ser. B 97 (2007); Open Problem Garden, list_hadwiger_conjecture.

A graph G is k-choosable if it has a proper colouring from all lists of at least k colours on its
vertices.  The choice number ch(G) is the minimum k such that G is k-choosable.

Conjecture: there is a constant c >= 1 such that, for every t, every K_t-minor-free graph G
satisfies ch(G) <= c t.

Encoding.  Graphs are finite and simple.  The constant is an integer, without loss of generality.
"ch(G) = m" is a relation between G and m. *)

From GraphTheory Require Import digraph sgraph minor.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/chromatic.v *)

(** [f] is a proper colouring from the lists [L]. *)
Definition proper_list_coloring
    (G : sgraph) (C : finType) (L : G -> {set C}) (f : G -> C) : Prop :=
  (forall v : G, f v \in L v) /\
  (forall x y : G, x -- y -> f x != f y).

(** [G] has a proper colouring from the lists [L]. *)
Definition list_colorable (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists f : G -> C, proper_list_coloring L f.

(** [G] is [k]-choosable. *)
Definition choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> list_colorable L.

(** The choice number (list chromatic number) of [G] is [m]. *)
Definition choice_number (G : sgraph) (m : nat) : Prop :=
  choosable G m /\ (forall k, choosable G k -> m <= k).

(** ** Statement *)

Definition OPG_hadwiger_list_kt_minor_free_choosable : Prop :=
  exists c : nat, 1 <= c /\
    forall (G : sgraph) (t chG : nat),
      ~ minor G 'K_t -> choice_number G chG -> chG <= c * t.
