(** * Unions of triangle-free graphs

Erdős, Hajnal, "On decomposition of graphs", Acta Math. Acad. Sci. Hungar. 18 (1967), 359-377;
Open Problem Garden, unions_of_triangle_free_graphs.

Question: is there a graph that has no subgraph isomorphic to K_4 and is not a union of countably
many triangle-free graphs?

The proposition states the positive answer.

Encoding.  Graphs are simple, with an arbitrary type of vertices and an adjacency relation in
[Prop].  A graph is a union of countably many triangle-free graphs if and only if its edges can be
partitioned into countably many sets without triangle: this partition is given by a symmetric
function that colours the pairs of vertices with natural numbers. *)

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

(** ** Definitions specific to the conjecture *)

(** [G] has no subgraph isomorphic to the complete graph on 4 vertices. *)
Definition iK4_free (G : iGraph) : Prop :=
  ~ exists a b c d : ivertex G,
      [/\ iedge a b, iedge a c, iedge a d, iedge b c & iedge b d /\ iedge c d].

(** [G] is the union of countably many triangle-free graphs: a colouring of its edges with natural
    numbers has no monochromatic triangle. *)
Definition countable_triangle_free_union (G : iGraph) : Prop :=
  exists col : ivertex G -> ivertex G -> nat,
    (forall x y, col x y = col y x) /\
    (forall x y z : ivertex G, iedge x y -> iedge y z -> iedge x z ->
       col x y = col y z -> col x y = col x z -> False).

(** ** Statement *)

Definition OPG_k4_free_countable_union_triangle_free : Prop :=
  exists G : iGraph, iK4_free G /\ ~ countable_triangle_free_union G.
