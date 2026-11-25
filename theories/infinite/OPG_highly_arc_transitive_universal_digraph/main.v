(** * Universal highly arc-transitive digraphs

Cameron, Praeger, Wormald, "Infinite highly arc transitive digraphs and universal covering
digraphs", Combinatorica 13 (1993), 377-396; Open Problem Garden,
universal_highly_arc_transitive_digraphs.

An s-arc of a digraph is a sequence x_0, ..., x_s of vertices such that (x_i,x_{i+1}) is an arc for
0 <= i <= s-1 and x_{i-1} <> x_{i+1} for 1 <= i <= s-1.  A digraph is highly arc-transitive if, for
all s >= 0, its automorphism group is transitive on the s-arcs.  An alternating walk is a walk
v_0, e_1, v_1, ..., v_m such that, for 1 <= i <= m-1, the vertex v_i is the head of both e_i and
e_{i+1} or the tail of both.  A digraph is universal if for all arcs e and f, some alternating walk
contains both e and f.  It is locally finite if all in-degrees and out-degrees are finite.

Question: is there a locally finite highly arc-transitive digraph that is universal?

The proposition states the positive answer.

Encoding.  Digraphs have no loop, an arbitrary type of vertices and an arc relation in [Prop].
Two guards are implicit in the source.  The digraph has at least one arc: otherwise a single vertex
would be an answer.  It has no two opposite arcs: otherwise a triangle with both arcs between any
two vertices would be an answer.  Then the condition x_{i-1} <> x_{i+1} is automatic, hence high
arc-transitivity is stated with all directed walks x_0, ..., x_s.  With this definition, the second
guard need not be written: a highly arc-transitive digraph with two opposite arcs is a disjoint
union of directed cycles of length 2, and is not universal.  Nor is it necessary to require that the
digraph is infinite: the finite highly arc-transitive digraphs with arcs are disjoint unions of
directed cycles, and are not universal.

An alternating walk is a sequence of vertices with a boolean that gives the direction of its first
arc: forward if it is true, backward otherwise. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/infinite.v *)

(** The set [P] is finite. *)
Definition ifinite_set (T : Type) (P : T -> Prop) : Prop :=
  exists (n : nat) (g : 'I_n -> T), forall x, P x -> exists i : 'I_n, g i = x.

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

(** ** Definitions specific to the conjecture *)

(** The sequence [x :: p] is an alternating walk that starts with a forward arc if [b] is true, with
    a backward arc otherwise. *)
Fixpoint alternating_walk (D : iDigraph) (b : bool) (x : idi_vertex D) (p : seq (idi_vertex D)) :
    Prop :=
  match p with
  | [::] => True
  | y :: p' => (if b then idi_arc x y else idi_arc y x) /\ alternating_walk (~~ b) y p'
  end.

(** The alternating walk [x :: p], with the direction [b] of its first arc, contains the arc from
    [u] to [v]. *)
Fixpoint alternating_walk_uses (D : iDigraph) (b : bool) (x : idi_vertex D)
    (p : seq (idi_vertex D)) (u v : idi_vertex D) : Prop :=
  match p with
  | [::] => False
  | y :: p' =>
      (if b then x = u /\ y = v else y = u /\ x = v) \/ alternating_walk_uses (~~ b) y p' u v
  end.

(** For all arcs, some alternating walk contains both. *)
Definition universal_digraph (D : iDigraph) : Prop :=
  forall u1 v1 u2 v2 : idi_vertex D, idi_arc u1 v1 -> idi_arc u2 v2 ->
    exists (b : bool) (x : idi_vertex D) (p : seq (idi_vertex D)),
      [/\ alternating_walk b x p, alternating_walk_uses b x p u1 v1
        & alternating_walk_uses b x p u2 v2].

(** ** Statement *)

Definition OPG_highly_arc_transitive_universal_digraph : Prop :=
  exists D : iDigraph,
    [/\ exists u v : idi_vertex D, idi_arc u v, idi_locally_finite D, highly_arc_transitive D
      & universal_digraph D].
