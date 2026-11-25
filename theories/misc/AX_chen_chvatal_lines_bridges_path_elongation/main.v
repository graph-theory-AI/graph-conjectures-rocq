(** * Lines and bridges: generation of the counterexamples

Aboulker, Matamala, Rochet, Zamora, "A new class of graphs that satisfies the Chen-Chvátal
conjecture", arXiv:1606.06011, open question (1606.06011__01).

Let G be a connected graph.  For vertices a, b, c of G, b is between a and c if
d(a,b) + d(b,c) = d(a,c).  The line through two distinct vertices a and b consists of a, b and
the vertices x such that one of a, b, x is between the two others.  Let ℓ(G) be the number of
distinct lines of G, and br(G) its number of bridges.

Question: can all the connected graphs G such that ℓ(G) + br(G) < |G| be obtained from a finite
set of graphs by replacing a bridge by a path of arbitrary length?

The proposition states the positive answer.

Encoding.  The replacement of a bridge can be repeated, with different bridges.  The finite set
of graphs is replaced by a bound on the order of its graphs.  This is equivalent, as there are
finitely many graphs of bounded order up to isomorphism.  The graphs of the finite set need not
be counterexamples themselves. *)

From GraphTheory Require Import preliminaries digraph sgraph.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

Section Sequences.
Variable T : finType.
Implicit Types (s : seq T) (x y : T).

(** The elements of [s] other than [x] and [y]. *)
Definition seq_interior x y s : {set T} := [set:: s] :\: [set x; y].

(** The list of the pairs of consecutive elements of [s]: the edges of a walk. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

(** The set of the pairs of consecutive elements of [s]: the edge set of a walk. *)
Definition seq_edge_set s : {set {set T}} := [set e in seq_edge_list s].

End Sequences.

(** The vertices of [G] at distance at most [k] from [x]. *)
Definition ball (G : sgraph) (k : nat) (x : G) : {set G} := iter k (@closed_neigh_set G) [set x].

Lemma graph_dist_ex (G : sgraph) (x y : G) :
  exists k : nat, (y \in ball k x) || (k == #|G|).
Proof. by exists #|G|; rewrite eqxx orbT. Qed.

(** The distance of [x] and [y] ([#|G|] if they are in different components). *)
Definition graph_dist (G : sgraph) (x y : G) : nat :=
  ex_minn (graph_dist_ex x y).

(** [v] is on a shortest path from [u] to [w] ([G] is connected). *)
Definition metric_between (G : sgraph) (u v w : G) : bool :=
  graph_dist u v + graph_dist v w == graph_dist u w.

(** The line through [a] and [b] in the metric space of [G] (Chen and Chvatal): the vertices
    [x] such that one of [a], [b], [x] is between the two others. *)
Definition metric_line (G : sgraph) (a b : G) : {set G} :=
  [set x : G |
      metric_between a b x || metric_between a x b || metric_between x a b].

(** The number of lines of [G]. *)
Definition metric_line_count (G : sgraph) : nat :=
  #|[set L : {set G} |
      [exists a : G, [exists b : G, (a != b) && (L == metric_line a b)]]]|.

(** [e] is a bridge: an edge whose ends are in different components when it is deleted. *)
Definition bridge (G : sgraph) (e : {set G}) : bool :=
  (e \in E(G)) &&
  [exists x in e, exists y in e, ~~ connect (del_edges_rel e) x y].

(** The number of bridges of [G]. *)
Definition bridge_count (G : sgraph) : nat :=
  #|[set e : {set G} | bridge e]|.

(** ** Definitions specific to the conjecture *)

(** The elements of [s] other than the first and the last ones. *)
Definition seq_inner (T : finType) (s : seq T) : {set T} :=
  if s is a :: t then seq_interior a (last a t) s else set0.

(** [H] is obtained from [G] by replacing a bridge [ab] by a path of length at least 1 between
    [a] and [b], with new internal vertices: [f] is the embedding of the vertices of [G] and
    [f a :: p] is the path. *)
Definition one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint seq_inner (f a :: p) & [set y : H | [exists x : G, f x == y]]] /\
    (forall v : H, v \in f a :: p \/ exists x : G, v = f x) /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in seq_edge_set (f a :: p)) \/
      (exists x y : G,
        [set x; y] != [set a; b] /\
        x -- y /\
        u = f x /\
        v = f y).

(** The second graph is obtained from the first one by a sequence of replacements of bridges by
    paths. *)
Inductive generated_by_bridge_replacement : sgraph -> sgraph -> Prop :=
| generated_refl G :
    generated_by_bridge_replacement G G
| generated_step G H K :
    one_bridge_replacement G H ->
    generated_by_bridge_replacement H K ->
    generated_by_bridge_replacement G K.

(** [G] is connected and [ℓ(G) + br(G) < |G|]. *)
Definition counterexample_to_lines_bridges_bound (G : sgraph) : Prop :=
  connected [set: G] /\ metric_line_count G + bridge_count G < #|G|.

(** ** Statement *)

Definition AX_chen_chvatal_lines_bridges_path_elongation : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        generated_by_bridge_replacement seed G.
