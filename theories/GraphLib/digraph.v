(** * Digraphs

Digraphs are those of GraphTheory ([diGraph]): a finite type of vertices with a boolean
edge relation [--].  Digons and loops are allowed, parallel edges are not represented. *)

From GraphTheory Require Import digraph.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

(** ** Definitions *)

(** [D] has no directed cycle: no edge [u -- v] such that [v] reaches [u]
    (a loop or a digon is a directed cycle). *)
Definition acyclic (D : diGraph) : bool :=
  [forall u : D, forall v : D, (u -- v) ==> ~~ connect (--) v u].

(** The dichromatic number of [D] is at most [k]: the vertices can be coloured with [k]
    colours so that each colour class induces an acyclic digraph. *)
Definition dicolorable (D : diGraph) (k : nat) : Prop :=
  exists col : D -> 'I_k, forall i : 'I_k, acyclic (induced [set v | col v == i]).

(** The fractional dichromatic number of [D] is at most [p]: nonnegative weights on the
    sets inducing an acyclic digraph, of total at most [p], cover each vertex with weight
    at least 1.  Weights are taken in an ordered field [R]. *)
Definition frac_dicolorable (R : realFieldType) (D : diGraph) (p : R) : Prop :=
  (exists x : {set D} -> R,
    [/\ forall A : {set D}, 0 <= x A,
        forall v : D, 1 <= \sum_(A : {set D} | acyclic (induced A) && (v \in A)) x A
      & \sum_(A : {set D} | acyclic (induced A)) x A <= p])%R.

(** ** Acyclic digraphs *)

(** [acyclic] is the absence of directed cycles (as sequences of vertices). *)
Lemma acyclicP (D : diGraph) :
  reflect (forall c : seq D, c != [::] -> ~~ cycle (--) c) (acyclic D).
Proof.
apply: (iffP forallP) => [ac [//|u c] _|nc u].
- apply/negP; rewrite /= rcons_path => /andP[pc lu].
  have /forallP/(_ u)/implyP/(_ lu)/negP := ac (last u c).
  by apply; apply/connectP; exists c.
- apply/forallP => v; apply/implyP => uv; apply/negP => /connectP[p pp lp].
  have /negP := nc (v :: p) isT; apply.
  by rewrite /= rcons_path pp -lp.
Qed.

(** A digraph is acyclic iff it has a numbering that increases along the edges
    (a topological order). *)
Lemma acyclic_rankP (D : diGraph) :
  reflect (exists phi : D -> nat, forall u v, u -- v -> phi u < phi v) (acyclic D).
Proof.
apply: (iffP forallP) => [ac|[phi inc] u].
- exists (fun v => #|[set w | connect (--) w v]|) => u v uv.
  apply/proper_card/properP; split.
    by apply/subsetP => w; rewrite !inE => /connect_trans; apply; apply: connect1.
  exists v; rewrite !inE ?connect0 //.
  by have /forallP/(_ v)/implyP/(_ uv) := ac u.
- apply/forallP => v; apply/implyP => uv; apply/negP => /connectP[p pp lp].
  suff: phi v <= phi u by rewrite leqNgt inc.
  rewrite lp; elim: p v pp {uv lp} => //= w p IH v /andP[vw pp].
  exact: leq_trans (ltnW (inc _ _ vw)) (IH _ pp).
Qed.

(** The same for induced subdigraphs. *)
Lemma acyclic_inducedP (D : diGraph) (A : {set D}) :
  reflect (exists phi : D -> nat, {in A &, forall u v, u -- v -> phi u < phi v})
          (acyclic (induced A)).
Proof.
apply: (iffP (acyclic_rankP _)) => -[phi inc]; last first.
  by exists (fun u => phi (val u)) => u v; apply: inc; apply: valP.
exists (fun u => if insub u is Some u' then phi u' else 0) => u v uA vA uv.
by rewrite (insubT (mem A) uA) (insubT (mem A) vA); apply: inc.
Qed.
