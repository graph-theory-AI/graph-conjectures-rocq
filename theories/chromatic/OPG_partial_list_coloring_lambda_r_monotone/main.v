(** * Partial list colouring: the ratios λ_t / t

Iradmusa, "A note on partial list colorings", Australas. J. Combin. 46 (2010); Open Problem Garden,
partial_list_coloring_0.

The list chromatic number χ_l(G) is the minimum k such that G has a proper colouring from all lists
of at least k colours on its vertices.  For a list assignment L of G, let λ_L be the maximum number
of vertices of an induced subgraph of G that has a proper colouring from L.  Let λ_t be the minimum
of λ_L for the list assignments L such that |L(v)| = t for every vertex v.

Conjecture: if 1 <= r <= s <= χ_l(G), then λ_r / r >= λ_s / s.

Encoding.  Graphs are finite and simple.  The inequality is multiplied by r s.  χ_l(G) and λ_t are
given by relations. *)

From GraphTheory Require Import digraph sgraph.
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

(** ** Definitions specific to the conjecture *)

(** [mu] is the maximum number of vertices of [G] that can be coloured from the lists [L]
    (λ_L). *)
Definition colourable_count (G : sgraph) (C : finType) (L : G -> {set C}) (mu : nat) : Prop :=
  (exists W : {set G}, list_colorable (fun v : induced W => L (val v)) /\ #|W| = mu) /\
  (forall W : {set G}, list_colorable (fun v : induced W => L (val v)) -> #|W| <= mu).

(** [lam] is λ_t: the minimum of λ_L for the list assignments [L] with lists of size [t]. *)
Definition is_lambda (G : sgraph) (t lam : nat) : Prop :=
  (exists (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) /\ colourable_count L lam) /\
  (forall (C : finType) (L : G -> {set C}) (mu : nat),
      (forall v : G, #|L v| = t) -> colourable_count L mu -> lam <= mu).

(** ** Statement *)

Definition OPG_partial_list_coloring_lambda_r_monotone : Prop :=
  forall (G : sgraph) (r s cl lr ls : nat),
    choice_number G cl ->
    1 <= r -> r <= s -> s <= cl ->
    is_lambda G r lr -> is_lambda G s ls ->
    r * ls <= s * lr.
