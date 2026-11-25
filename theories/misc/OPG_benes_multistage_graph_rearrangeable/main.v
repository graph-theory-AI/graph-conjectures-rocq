(** * Beneš Conjecture (graph-theoretic form)

Beneš, "Proving the rearrangeability of connecting networks by group calculation", Bell Syst.
Tech. J. 54 (1975); Open Problem Garden, bene_conjecture_graph_theoretic_form_0, Conjecture (◇).

A 2-stage graph L is a bipartite graph between sources and targets.  It is ordered if both parts
are linearly ordered.  If both parts have size t, the graph L^m is the concatenation of m copies
of L, with m + 1 stages of size t: the targets of each copy are the sources of the next one,
according to the orders.  A path of L^m is plain if it goes from a source to a target (vertices
of the first and last stages) through each stage exactly once.  The graph L^m is externally
connected if there is a plain path from every source to every target.  A mask of L^m is a
bipartite multigraph between its sources and its targets where each vertex has the same degree as
in L^m.  The graph L^m is rearrangeable if, for every mask, there are mutually edge-disjoint
plain paths that join the ends of the edges of the mask.

Conjecture (◇): let L be a simple regular ordered 2-stage graph.  If L^m is externally connected
for some m >= 1, then L^(2m) is rearrangeable.

Encoding.  A simple ordered 2-stage graph with parts of size t > 0 is a relation on {0,...,t-1},
between sources and targets.  If it is d-regular, the edges of a mask are indexed by the pairs
(i,a) with 0 <= i < t and 0 <= a < d: the d edges at the source i are (i,0),...,(i,d-1), and the
mask is the map that gives the target of each edge.  The problem (†) of the same entry (find a
sufficient condition for rearrangeability) is not stated. *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definitions copied from GraphLib/misc.v *)

(** [m] is a mask: the edge [(i, a)] joins the input [i] of the first stage to the output
    [m (i, a)] of the last one, and each output of the last stage has degree [k]. *)
Definition is_mask (t k : nat) (m : 'I_t * 'I_k -> 'I_t) : Prop :=
  forall j : 'I_t, #|[set x | m x == j]| = k.

(** The paths [route x] through [s] stages connect the ends of the edges [x] of the mask [m], and
    they are edge-disjoint. *)
Definition mask_routing (t k : nat) (S : rel 'I_t) (s : nat) (m : 'I_t * 'I_k -> 'I_t)
  (route : 'I_t * 'I_k -> nat -> 'I_t) : Prop :=
  [/\ forall x, route x 0 = x.1,
      forall x, route x s = m x,
      forall x q, q < s -> S (route x q) (route x q.+1) &
      forall x y q, q < s ->
        route x q = route y q -> route x q.+1 = route y q.+1 -> x = y].

(** The network with [s] stages is rearrangeable: every mask has a routing (the bipartite graph
    is meant to be [k]-regular). *)
Definition mask_rearrangeable (t k : nat) (S : rel 'I_t) (s : nat) : Prop :=
  forall m : 'I_t * 'I_k -> 'I_t, is_mask m -> exists route, mask_routing S s m route.

(** ** Definitions specific to the conjecture *)

(** The 2-stage graph [S] is [d]-regular. *)
Definition stage_regular {t : nat} (S : rel 'I_t) (d : nat) : Prop :=
  (forall i : 'I_t, #|[set j : 'I_t | S i j]| = d) /\
  (forall j : 'I_t, #|[set i : 'I_t | S i j]| = d).

(** There is a plain path through [m] copies of [S] from the source [a] to the target [b]. *)
Definition stage_reachable {t : nat} (S : rel 'I_t) (m : nat) (a b : 'I_t) : Prop :=
  exists w : seq 'I_t, [/\ size w = m, path S a w & last a w = b].

(** The concatenation of [m] copies of [S] is externally connected. *)
Definition externally_connected {t : nat} (S : rel 'I_t) (m : nat) : Prop :=
  forall a b : 'I_t, stage_reachable S m a b.

(** ** Statement *)

Definition OPG_benes_multistage_graph_rearrangeable : Prop :=
  forall (t : nat) (L : rel 'I_t) (d : nat),
    0 < t ->
    stage_regular L d ->
    forall m : nat,
      1 <= m ->
      externally_connected L m ->
      mask_rearrangeable d L (2 * m).
