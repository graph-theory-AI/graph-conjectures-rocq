(** * Infinite graphs

Infinite simple graphs ([iGraph]) have an arbitrary type of vertices and an adjacency relation
in [Prop], symmetric and irreflexive.  Sets of vertices are predicates.  Cardinalities are
compared by injections. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Infinite graphs *)

(** Simple graphs, possibly infinite. *)
Record iGraph := Build_iGraph {
  ivertex : Type;
  iedge : ivertex -> ivertex -> Prop;
  iedge_sym : forall x y, iedge x y -> iedge y x;
  iedge_irrefl : forall x, ~ iedge x x }.

(** [P] is at most as large as [Q]. *)
Definition icard_le (A B : Type) (P : A -> Prop) (Q : B -> Prop) : Prop :=
  exists f : {x : A | P x} -> {y : B | Q y}, injective f.

(** [G] is countable (possibly finite). *)
Definition countable_graph (G : iGraph) : Prop :=
  exists f : ivertex G -> nat, injective f.

(** [G] is infinite. *)
Definition infinite_graph (G : iGraph) : Prop :=
  exists f : nat -> ivertex G, injective f.

(** The set [P] is finite. *)
Definition ifinite_set (T : Type) (P : T -> Prop) : Prop :=
  exists (n : nat) (g : 'I_n -> T), forall x, P x -> exists i : 'I_n, g i = x.

(** There is a walk with vertices in [P]. *)
Inductive ireach (G : iGraph) (P : ivertex G -> Prop) : ivertex G -> ivertex G -> Prop :=
  | ireach0 x : P x -> ireach P x x
  | ireachS x y z : ireach P x y -> iedge y z -> P z -> ireach P x z.

(** [P] induces a connected subgraph. *)
Definition iconnected_set (G : iGraph) (P : ivertex G -> Prop) : Prop :=
  forall x y, P x -> P y -> ireach P x y.

(** [G] and [H] are isomorphic. *)
Definition iisomorphic (G H : iGraph) : Prop :=
  exists f : ivertex G -> ivertex H,
    bijective f /\ (forall x y : ivertex G, iedge x y <-> iedge (f x) (f y)).

(** [G] is isomorphic to a subgraph of [H]. *)
Definition iembeds (G H : iGraph) : Prop :=
  exists f : ivertex G -> ivertex H,
    injective f /\ forall x y : ivertex G, iedge x y -> iedge (f x) (f y).

(** The branch sets [b h] show that [H] is a minor of [G]: they are nonempty, connected and
    pairwise disjoint, and there is an edge between the branch sets of adjacent vertices. *)
Definition iminor_model (G H : iGraph) (b : ivertex H -> ivertex G -> Prop) : Prop :=
  [/\ (forall h : ivertex H, exists x, b h x),
      (forall h : ivertex H, iconnected_set (b h)),
      (forall (h1 h2 : ivertex H) (x : ivertex G), b h1 x -> b h2 x -> h1 = h2)
    & (forall h1 h2 : ivertex H, iedge h1 h2 ->
         exists x y, b h1 x /\ b h2 y /\ iedge x y) ].

(** ** Rays and ends *)

(** [r] is a ray: a one-way infinite path. *)
Definition ray (G : iGraph) (r : nat -> ivertex G) : Prop :=
  injective r /\ forall n, iedge (r n) (r n.+1).

(** The rays [r] and [r'] are in the same end: for each finite set [S], they have tails in the
    same component of the complement of [S]. *)
Definition end_equiv (G : iGraph) (r r' : nat -> ivertex G) : Prop :=
  forall S : ivertex G -> Prop, ifinite_set S ->
    exists N : nat, forall n : nat, N <= n ->
      exists m : nat, N <= m /\ ireach (fun v => ~ S v) (r n) (r' m).

(** ** Unfriendly partitions *)

(** The partition [p] is unfriendly: each vertex has at least as many neighbours in the other
    part as in its own part. *)
Definition unfriendly (G : iGraph) (p : ivertex G -> bool) : Prop :=
  forall x : ivertex G,
    icard_le (fun w => iedge x w /\ p w = p x) (fun w => iedge x w /\ p w <> p x).

(** ** Reconstruction *)

(** [G] minus [v] and [H] minus [w] are isomorphic. *)
Definition ivertex_deleted_iso (G H : iGraph) (v : ivertex G) (w : ivertex H) : Prop :=
  exists f : ivertex G -> ivertex H,
    [/\ forall x, x <> v -> f x <> w,
        forall x y, x <> v -> y <> v -> f x = f y -> x = y,
        forall y, y <> w -> exists x, x <> v /\ f x = y &
        forall x y, x <> v -> y <> v -> (iedge x y <-> iedge (f x) (f y))].

(** [G] and [H] are hypomorphic: for some bijection between their vertices, the subgraphs
    obtained by deleting corresponding vertices are isomorphic. *)
Definition ihypomorphic (G H : iGraph) : Prop :=
  exists phi : ivertex G -> ivertex H,
    bijective phi /\ forall v : ivertex G, @ivertex_deleted_iso G H v (phi v).

(** ** Infinite hypergraphs *)

(** Hypergraphs, possibly infinite, with an incidence relation. *)
Record iHypergraph := Build_iHypergraph {
  ihg_vertex : Type;
  ihg_edge : Type;
  ihg_incident : ihg_edge -> ihg_vertex -> Prop }.

(** [F] is a matching: distinct edges of [F] have no common vertex. *)
Definition ihg_matching (H : iHypergraph) (F : ihg_edge H -> Prop) : Prop :=
  forall e1 e2, F e1 -> F e2 -> (exists v, ihg_incident e1 v /\ ihg_incident e2 v) -> e1 = e2.

(** [X] is a vertex cover: it meets all edges. *)
Definition ihg_cover (H : iHypergraph) (X : ihg_vertex H -> Prop) : Prop :=
  forall e : ihg_edge H, exists v, X v /\ ihg_incident e v.

(** The matching [F] is strongly maximal: for each matching [F'], the set [F' \ F] is at most as
    large as [F \ F']. *)
Definition strongly_maximal_matching (H : iHypergraph) (F : ihg_edge H -> Prop) : Prop :=
  ihg_matching F /\
  forall F' : ihg_edge H -> Prop, ihg_matching F' ->
    icard_le (fun e => F' e /\ ~ F e) (fun e => F e /\ ~ F' e).

(** The cover [X] is strongly minimal: for each cover [X'], the set [X \ X'] is at most as large
    as [X' \ X]. *)
Definition strongly_minimal_cover (H : iHypergraph) (X : ihg_vertex H -> Prop) : Prop :=
  ihg_cover X /\
  forall X' : ihg_vertex H -> Prop, ihg_cover X' ->
    icard_le (fun v => X v /\ ~ X' v) (fun v => X' v /\ ~ X v).

(** ** Infinite digraphs *)

(** Digraphs without loops, possibly infinite. *)
Record iDigraph := Build_iDigraph {
  idi_vertex : Type;
  idi_arc : idi_vertex -> idi_vertex -> Prop;
  idi_arc_irrefl : forall x, ~ idi_arc x x }.

(** [f] is an automorphism of [D]. *)
Definition idi_automorphism (D : iDigraph) (f : idi_vertex D -> idi_vertex D) : Prop :=
  bijective f /\ forall x y, idi_arc x y <-> idi_arc (f x) (f y).

(** [p] is a directed walk, as a sequence of vertices (possibly empty). *)
Fixpoint idi_walk (D : iDigraph) (p : seq (idi_vertex D)) : Prop :=
  match p with
  | [::] => True
  | x :: p' => match p' with
               | [::] => True
               | y :: _ => idi_arc x y /\ idi_walk p'
               end
  end.

(** [D] is highly arc-transitive: for all directed walks of the same length, some automorphism
    maps the first one to the second one. *)
Definition highly_arc_transitive (D : iDigraph) : Prop :=
  forall p q : seq (idi_vertex D),
    idi_walk p -> idi_walk q -> size p = size q ->
    exists f : idi_vertex D -> idi_vertex D, idi_automorphism f /\ map f p = q.

(** All in-degrees and out-degrees are finite. *)
Definition idi_locally_finite (D : iDigraph) : Prop :=
  forall x : idi_vertex D, ifinite_set (idi_arc x) /\ ifinite_set (fun y => idi_arc y x).
