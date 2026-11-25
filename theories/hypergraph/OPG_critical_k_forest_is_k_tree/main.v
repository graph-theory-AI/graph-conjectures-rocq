(** * Critical k-forests are tight

Strausz; Open Problem Garden, are_critical_k_forests_tight.

Let H = (V,E) be a k-uniform hypergraph.  It is a k-forest (Lovász) if, for every edge e, there is
a colouring of V with k colours such that e is the only edge whose vertices have all k colours (a
2-forest is an acyclic graph).  A k-forest is critical if adding any set of k vertices as a new
edge gives a hypergraph that is not a k-forest.  The heterochromatic number of H (Neumann-Lara) is
the least number c such that every colouring of V with exactly c colours has an edge whose
vertices have distinct colours.  H is tight if its heterochromatic number is k (a 2-uniform
hypergraph is tight if and only if it is connected).  A k-tree is a tight k-forest.

Conjecture: every critical k-forest is a k-tree.

Encoding.  A colouring with exactly k colours is a surjection of V onto k colours.  A colouring
with fewer colours has no edge with k distinct colours.  Hence, when |V| >= k, the hypergraph is
tight if and only if every colouring with exactly k colours has an edge with all k colours, which
is the definition used here.  When |V| < k there are no edges and the statement is trivially
true. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}).

(** [E] is [k]-uniform: every edge has [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

End Hypergraph.

(** ** Definitions specific to the conjecture *)

Section KForests.
Variables (T : finType) (k : nat).
Implicit Types (E : {set {set T}}) (e : {set T}) (col : T -> 'I_k).

(** The vertices of [e] have all [k] colours. *)
Definition all_colors col e : bool := [forall i : 'I_k, [exists v in e, col v == i]].

(** [E] is a [k]-forest: it is [k]-uniform and, for each edge, some colouring with [k] colours is
    such that this edge is the only one with all the colours. *)
Definition k_forest E : Prop :=
  hg_uniform E k /\
  forall e, e \in E ->
    exists col : T -> 'I_k, forall f : {set T}, f \in E -> (all_colors col f <-> f = e).

(** [E] is a critical [k]-forest: no edge can be added to it. *)
Definition critical_k_forest E : Prop :=
  k_forest E /\ forall e, #|e| = k -> e \notin E -> ~ k_forest (e |: E).

(** [E] is tight: every colouring with exactly [k] colours has an edge with all the colours. *)
Definition hg_tight E : Prop :=
  forall col : T -> 'I_k, (forall i : 'I_k, exists v : T, col v = i) ->
    exists2 e, e \in E & all_colors col e.

(** [E] is a [k]-tree. *)
Definition k_tree E : Prop := k_forest E /\ hg_tight E.

End KForests.

(** ** Statement *)

Definition OPG_critical_k_forest_is_k_tree : Prop :=
  forall (k : nat) (T : finType) (E : {set {set T}}),
    critical_k_forest k E -> k_tree k E.
