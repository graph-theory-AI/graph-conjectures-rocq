(** * Frankl's union-closed sets conjecture

Frankl (1979); Open Problem Garden, frankls_union_closed_sets_conjecture.

Conjecture: let F be a finite family of finite sets, not all empty, that is closed under union.
Then some element x belongs to at least half of the members of F.

Encoding.  F is a set of subsets of a finite type.  "At least half" is |F| <= 2 |F_x| where F_x is
the set of members of F that contain x. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/hypergraph.v *)

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}).

(** [E] is closed under union. *)
Definition union_closed E : Prop :=
  forall A B : {set T}, A \in E -> B \in E -> (A :|: B) \in E.

End Hypergraph.

(** ** Statement *)

Definition OPG_frankl_union_closed_frequent_element : Prop :=
  forall (T : finType) (F : {set {set T}}),
    union_closed F ->
    (exists2 A : {set T}, A \in F & A != set0) ->
    exists x : T, #|F| <= 2 * #|[set A in F | x \in A]|.
