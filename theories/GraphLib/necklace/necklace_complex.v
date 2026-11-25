(** * The complexes K and L, and the statement of the Z_p-simplotopal Tucker lemma

    F. Meunier, "Simplotopal maps and necklace splitting", Discrete Mathematics 323 (2014),
    Section 3.2 and Theorem 3.3.  The necklace has [n] beads of [t] types, and there are [p]
    thieves.

    - [R] is the star with centre [o] and [p] paths of length [n]; its vertices are encoded as
      [cut := option ('I_n * 'I_p)], where [None] is [o] and [Some (k, r)] is the vertex (k+1, r)
      of the paper.  Its edges are the pairs [{slide x, x}] for [x <> None].
    - The vertices of R^N, for N = t(p-1)+1, are the functions [vertex := {ffun 'I_N -> cut}].  A
      face is given by its top vertex [u] and the set [S] of the coordinates that move.
    - K is the part of R^N where a coordinate covers the whole necklace ([in_X]), and L is the
      product of [t] simplices on the thieves.
    - [zp_tucker] states that an equivariant simplotopal map from K to L maps some face of K onto
      L (Theorem 3.3; it is proved in zp_tucker.v for [p] prime). *)

From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NecklaceComplex.
Variables (n t p : nat).
Hypothesis p_gt0 : 0 < p.

Definition N := (t * p.-1).+1.

Definition cut := option ('I_n * 'I_p).
Definition vertex := {ffun 'I_N -> cut}.

(** The cut [x] lies at or after bead [b]. *)
Definition covers (x : cut) (b : 'I_n) : bool :=
  if x is Some (k, _) then b <= k else false.

Definition in_X (v : vertex) : bool :=
  [forall b : 'I_n, [exists j : 'I_N, covers (v j) b]].

Definition ordp (k : 'I_n) : 'I_n :=
  Ordinal (leq_ltn_trans (leq_pred k) (ltn_ord k)).

(** The lower end of the edge of [R] whose upper end is [x]. *)
Definition slide (x : cut) : cut :=
  if x is Some (k, r) then (if k == 0 :> nat then None else Some (ordp k, r))
  else None.

Definition vert (u : vertex) (T : {set 'I_N}) : vertex :=
  [ffun j => if j \in T then slide (u j) else u j].

Definition face (u : vertex) (S : {set 'I_N}) : bool :=
  [forall j in S, u j != None] && [forall T in powerset S, in_X (vert u T)].

Definition shiftp (r : 'I_p) : 'I_p := Ordinal (ltn_pmod r.+1 p_gt0).

Definition shift_cut (x : cut) : cut := omap (fun kr => (kr.1, shiftp kr.2)) x.

Definition shift_vertex (v : vertex) : vertex := [ffun j => shift_cut (v j)].

Definition image_set (mu : vertex -> 'I_t -> 'I_p) (u : vertex) (S : {set 'I_N})
    (i : 'I_t) : {set 'I_p} :=
  [set mu (vert u T) i | T in powerset S].

Definition equivariant (mu : vertex -> 'I_t -> 'I_p) : Prop :=
  forall v, in_X v -> forall i, mu (shift_vertex v) i = shiftp (mu v i).

Definition simplotopal (mu : vertex -> 'I_t -> 'I_p) : Prop :=
  forall u S, face u S ->
    (\sum_(i : 'I_t) (#|image_set mu u S i| - 1) <= #|S|)%N.

(** Theorem 3.3 of Meunier (2014), for [K] and [L]. *)
Definition zp_tucker : Prop :=
  0 < n ->
  forall mu : vertex -> 'I_t -> 'I_p,
    equivariant mu -> simplotopal mu ->
    exists (u : vertex) (S : {set 'I_N}),
      [/\ face u S, #|S| = t * p.-1 & forall i, image_set mu u S i = setT].

End NecklaceComplex.

Arguments cut : clear implicits.
Arguments covers {n p} x b.
