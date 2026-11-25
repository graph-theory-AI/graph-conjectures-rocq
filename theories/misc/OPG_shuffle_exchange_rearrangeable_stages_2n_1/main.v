(** * Shuffle-exchange conjecture

Stone, "Parallel processing with the perfect shuffle", IEEE Trans. on Computers C-20 (1971);
Beneš, "Proving the rearrangeability of connecting networks by group calculation", Bell Syst.
Tech. J. 54 (1975);
Open Problem Garden, shuffle_exchange_conjecture_graph_theoretic_form.

Let k,n >= 2 and t = k^(n-1).  The graph SE(k,n) is the k-regular bipartite graph with parts
{u_0,...,u_{t-1}} and {v_0,...,v_{t-1}}, where u_i and v_j are adjacent if and only if
(j - ki) mod t < k.  For r >= 2, SE(k,n)^{r-1} is the concatenation of r-1 copies of SE(k,n):
it has r stages of t vertices.

A mask is a k-regular bipartite multigraph between the first and the last stages.  The graph
SE(k,n)^{r-1} is rearrangeable if, for every mask, there are k^n mutually edge-disjoint paths
that connect the ends of the k^n edges of the mask.  Let r(k,n) be the smallest r >= 2 such that
SE(k,n)^{r-1} is rearrangeable.

Conjecture: r(k,n) = 2n-1 for all k,n >= 2.

Encoding.  The edges of a mask are indexed by the pairs (i,a) with 0 <= i < t and 0 <= a < k: the
k edges at the vertex i of the first stage are (i,0),...,(i,k-1), and the mask is the map that
gives the other end of each edge.  A path goes through the r stages in order: this is not a
restriction, as r-1 is the distance between the first and the last stages, and SE(k,n)^{r-1} has
exactly (r-1) k^n edges.  The proposition says that SE(k,n)^{2n-2} is rearrangeable and that
r >= 2n-1 whenever r >= 2 and SE(k,n)^{r-1} is rearrangeable. *)

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

(** The adjacency of the vertices [u_i] and [v_j] of the graph [SE(k,n)]: [(j - k i) mod t < k]
    with [t = k ^ (n - 1)]. *)
Definition shuffle_exchange_adj (k n : nat) : rel 'I_(k ^ (n - 1)) :=
  fun i j =>
    let t := k ^ (n - 1) in
    (val j + (t - (k * val i) %% t)) %% t < k.

(** ** Statement *)

Definition OPG_shuffle_exchange_rearrangeable_stages_2n_1 : Prop :=
  forall k n : nat,
    2 <= k -> 2 <= n ->
    mask_rearrangeable k (@shuffle_exchange_adj k n) (2 * n - 2) /\
    (forall r : nat,
      2 <= r -> mask_rearrangeable k (@shuffle_exchange_adj k n) (r - 1) -> 2 * n - 1 <= r).
