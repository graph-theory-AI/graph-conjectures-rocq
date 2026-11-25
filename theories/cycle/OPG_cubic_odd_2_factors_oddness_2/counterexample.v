(** * A ring of three Petersen graphs minus an edge

Let G consist of three copies of the Petersen graph minus an edge, joined by three edges into a
ring: the ends of the missing edge are 0 and 9 in each copy, and vertex 9 of copy i is joined to
vertex 0 of copy i+1.  A 2-factor F of G contains all three joining edges or none of them, since
any two of them form a cut.  In the latter case, F induces a 2-factor of the Petersen graph in each
copy, hence F consists of six cycles of length 5.  In the former case, F consists of a cycle of
length 15 through the joining edges and of a cycle of length 5 in each copy.  Thus all the cycles
of the 2-factors are odd, and the oddness of G is 4.

In Rocq, the 2-factors are enumerated by a backtracking search [partial] on lists of 45 booleans,
which represent the sets of edges, and the cycles of each of them are computed [check_factors].  A
circuit included in a 2-factor F is a component of F [circuit_comp].

The counterexample was found by computer search. *)

From GraphTheory Require Import mgraph.
From GraphTheory Require Import preliminaries digraph sgraph.
From GraphTheory Require skeleton.
From GC.cycle.OPG_cubic_odd_2_factors_oddness_2 Require Import main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ord_all m (k : 'I_m) (P : pred nat) : all P (iota 0 m) -> P k.
Proof. by move=> /allP h; apply: h; rewrite mem_iota ltn_ord. Qed.

Lemma ord_all2 m n (k : 'I_m) (l : 'I_n) (P : nat -> pred nat) :
  all (fun k => all (P k) (iota 0 n)) (iota 0 m) -> P k l.
Proof. by move=> /(ord_all k)/(ord_all l). Qed.

(** ** The graph *)

(** The edges of the Petersen graph, except the edge between 0 and 9. *)
Definition petersen_minus : seq (nat * nat) :=
  [:: (0, 1); (0, 2); (1, 3); (1, 4); (2, 5); (2, 6); (3, 6); (3, 7); (4, 5); (4, 8); (5, 7);
      (6, 8); (7, 9); (8, 9)].

(** The vertices of copy i are 10i, ..., 10i + 9; its edges are 15i, ..., 15i + 13, and edge
    15i + 14 joins it to copy i+1. *)
Definition edge_table : seq (nat * nat) := Eval compute in
  flatten [seq rcons [seq (10 * i + e.1, 10 * i + e.2) | e <- petersen_minus]
                     (10 * i + 9, 10 * (i.+1 %% 3)) | i <- iota 0 3].

Definition ends (k : nat) : nat * nat := nth (0, 0) edge_table k.

Definition G : mgraph :=
  {| vertex := 'I_30; edge := 'I_45;
     endpoint b k := inord (if b then (ends k).2 else (ends k).1);
     vlabel _ := tt; elabel _ := tt |}.

Definition at_ (v k : nat) : bool := ((ends k).1 == v) || ((ends k).2 == v).

(** The edges at each vertex. *)
Definition star_table : seq (seq nat) :=
  Eval compute in [seq [seq k <- iota 0 45 | at_ v k] | v <- iota 0 30].

Definition star (v : nat) : seq nat := nth [::] star_table v.

Lemma ends_lt (k : 'I_45) : ((ends k).1 < 30) && ((ends k).2 < 30) && ((ends k).1 != (ends k).2).
Proof.
exact: (ord_all k (P := fun k => ((ends k).1 < 30) && ((ends k).2 < 30)
  && ((ends k).1 != (ends k).2))).
Qed.

Lemma sourceE (k : edge G) : val (source k) = (ends k).1.
Proof. by rewrite /= inordK //; case/andP: (ends_lt k) => /andP[]. Qed.

Lemma targetE (k : edge G) : val (target k) = (ends k).2.
Proof. by rewrite /= inordK //; case/andP: (ends_lt k) => /andP[]. Qed.

Lemma starE (v : 'I_30) : star v = [seq k <- iota 0 45 | at_ v k].
Proof.
apply/eqP.
exact: (ord_all v (P := fun v => star v == [seq k <- iota 0 45 | at_ v k])).
Qed.

Lemma mem_star (v : G) (k : edge G) : (val k \in star v) = (source k == v) || (target k == v).
Proof.
by rewrite starE mem_filter mem_iota leq0n ltn_ord !andbT /at_ -sourceE -targetE !val_eqE.
Qed.

(** ** Sets of edges as lists of booleans *)

Definition bits (F : {set edge G}) : seq bool := [seq k \in F | k <- enum 'I_45].

Definition degree (b : seq bool) (v : nat) : nat := count (nth false b) (star v).

Lemma size_bits F : size (bits F) = 45.
Proof. by rewrite size_map size_enum_ord. Qed.

Lemma nth_bits F (k : 'I_45) : nth false (bits F) k = (k \in F).
Proof. by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum. Qed.

Lemma card_ord_pred n (P : pred nat) : #|[set k : 'I_n | P k]| = count P (iota 0 n).
Proof. by rewrite cardsE cardE size_filter -val_enum_ord count_map enumT. Qed.

Lemma degreeE F (v : G) : mdeg_in F v = degree (bits F) v.
Proof.
rewrite /degree starE count_filter /mdeg_in.
pose P (p : nat * nat -> nat) := [pred k | nth false (bits F) k & p (ends k) == val v].
have cE (p : nat * nat -> nat) (q : edge G -> G) : (forall k, val (q k) = p (ends k)) ->
    #|[set k in F | q k == v]| = count (P p) (iota 0 45).
  move=> qE; rewrite -card_ord_pred; apply: eq_card => k.
  by rewrite !inE /= nth_bits -val_eqE qE.
rewrite (cE Datatypes.fst _ sourceE) (cE Datatypes.snd _ targetE) -count_predUI.
rewrite [X in _ + X](eq_in_count (a2 := pred0)) ?count_pred0 ?addn0 => [k|].
  rewrite mem_iota => k45; have /andP[_] := ends_lt (Ordinal k45).
  by apply: contraNF => /andP[/andP[_ /eqP->] /andP[_ /eqP->]].
by apply: eq_count => k; rewrite /= -andb_orr.
Qed.

Lemma count_eq (T : eqType) (P Q : pred T) (s : seq T) : subpred P Q -> count P s = count Q s ->
  {in s, Q =1 P}.
Proof.
move=> PQ; elim: s => //= y s IH; have le := sub_count PQ s; have := PQ y.
case Py: (P y); case Qy: (Q y) => pq; rewrite ?add1n ?add0n => e x.
- by rewrite inE => /predU1P[->|]; [rewrite Py Qy|apply: IH; case: e].
- by have := pq isT.
- by rewrite e ltnn in le.
- by rewrite inE => /predU1P[->|]; [rewrite Py Qy|apply: IH].
Qed.

(** ** The 2-factors *)

(** The prefixes of length [m] of 2-factors: the degree of a vertex is checked when its last edge is
    decided. *)
Definition prefix_ok (m : nat) (p : seq bool) : bool :=
  all (fun v => has (leq m.+1) (star v) || (degree p v == 2)) [:: (ends m).1; (ends m).2].

Fixpoint partial (m : nat) : seq (seq bool) :=
  if m is m'.+1 then
    [seq p <- flatten [seq [:: rcons p true; rcons p false] | p <- partial m'] | prefix_ok m' p]
  else [:: [::]].

Definition factors : seq (seq bool) := Eval vm_compute in partial 45.

(** The edges sharing a vertex with each edge. *)
Definition adjacent_table : seq (seq nat) := Eval vm_compute in
  [seq undup (star (ends k).1 ++ star (ends k).2) | k <- iota 0 45].

Definition adjacent (k : nat) : seq nat := nth [::] adjacent_table k.

(** The edges of [b] adjacent to an edge of [K]. *)
Definition grow (b K : seq bool) : seq bool :=
  [seq nth false b l && has (nth false K) (adjacent l) | l <- iota 0 45].

(** The component of the edge [k] in [b]. *)
Definition component (b : seq bool) (k : nat) : seq bool :=
  iter 8 (grow b) (mkseq (pred1 k) 45).

(** The first edge of [b] that is not in [U]. *)
Definition first_edge (b U : seq bool) : nat :=
  find (fun l => nth false b l && ~~ nth false U l) (iota 0 45).

(** The components of [b] that do not meet [U], with their first edges. *)
Fixpoint components (n : nat) (b U : seq bool) : seq (nat * seq bool) :=
  let k := first_edge b U in
  if (n, k < 45) is (n'.+1, true) then
    let K := component b k in (k, K) :: components n' b [seq p.1 || p.2 | p <- zip U K]
  else [::].

(** The components of [b] are odd cycles, and there are at least three of them. *)
Definition three_odd_components (b : seq bool) : bool :=
  let Ks := components 6 b (nseq 45 false) in
  [&& all (fun p => [&& nth false b p.1, nth false p.2 p.1, grow b p.2 == p.2
                      & odd (count id p.2)]) Ks,
      all (fun l => nth false b l ==> has (fun p => nth false p.2 l) Ks) (iota 0 45),
      pairwise (fun p q => ~~ nth false p.2 q.1) Ks & 2 < size Ks].

Lemma check_factors : all three_odd_components factors.
Proof. by vm_compute. Qed.

Lemma mem_partial (b : seq bool) (n : nat) : size b = 45 ->
  (forall v : 'I_30, degree b v = 2) -> n <= 45 -> take n b \in partial n.
Proof.
move=> sz deg2; elim: n => [|n IH] n45; first by rewrite take0.
have {}IH := IH (ltnW n45); rewrite (take_nth false) ?sz // mem_filter; apply/andP; split.
  apply/allP => v v_n; have v30 : v < 30.
    case/andP: (ends_lt (Ordinal n45)) => /andP[lt1 lt2] _.
    by move: v_n; rewrite !inE => /orP[]/eqP->.
  case: (boolP (has _ _)) => //= /hasPn no; rewrite -(deg2 (Ordinal v30)); apply/eqP.
  apply: eq_in_count => k /no; rewrite -ltnNge ltnS => kn.
  by rewrite -take_nth ?sz // nth_take.
apply/flattenP; exists [:: rcons (take n b) true; rcons (take n b) false].
  by apply/mapP; exists (take n b).
by case: nth; rewrite !inE eqxx ?orbT.
Qed.

Lemma factorsE : factors = partial 45.
Proof. by vm_compute. Qed.

Lemma mem_factors F : two_factor F -> bits F \in factors.
Proof.
move=> tf; rewrite factorsE -[bits F]take_size size_bits.
by apply: mem_partial => // [|v]; rewrite ?size_bits // -degreeE.
Qed.

Lemma componentsP n b U p : p \in components n b U -> p.2 = component b p.1.
Proof.
elim: n U => [|n IH] U //; rewrite [components _ _ _]/components -/components.
by case: ltnP => // _; rewrite inE => /predU1P[->//|/IH].
Qed.

(** ** The circuits of a 2-factor *)

Lemma mem_adjacent (k l : edge G) : reflect
  (exists v : G, (val k \in star v) /\ (val l \in star v)) (val l \in adjacent k).
Proof.
have -> : adjacent k = undup (star (source k) ++ star (target k)).
  rewrite sourceE targetE; apply/eqP.
  exact: (ord_all k (P := fun k => adjacent k == undup (star (ends k).1 ++ star (ends k).2))).
rewrite mem_undup mem_cat; apply: (iffP orP) => [[]l_v|[v []]].
- by exists (source k); split; rewrite // mem_star eqxx.
- by exists (target k); split; rewrite // mem_star eqxx orbT.
by rewrite mem_star => /orP[]/eqP<-; [left|right].
Qed.

Lemma nth_grow b K (l : 'I_45) :
  nth false (grow b K) l = nth false b l && has (nth false K) (adjacent l).
Proof. by rewrite (nth_map 0) ?size_iota // nth_iota. Qed.

Lemma adjacent_lt k l : l \in adjacent k -> l < 45.
Proof.
case: (ltnP k 45) => [k45|k45]; last by rewrite /adjacent nth_default.
have := ord_all (Ordinal k45) (P := fun k => all (gtn 45) (adjacent k)) isT.
by move/allP/[apply].
Qed.

Lemma adjacent_sym (k l : edge G) : (val l \in adjacent k) = (val k \in adjacent l).
Proof. by apply/mem_adjacent/mem_adjacent => -[v [kv lv]]; exists v. Qed.

Section TwoFactor.

Variable F : {set edge G}.
Hypothesis tF : two_factor F.

(** A set of edges of [F] closed under adjacency contains the components of its elements. *)
Definition closed (S : {set edge G}) : Prop :=
  forall k l, k \in S -> l \in F -> val l \in adjacent k -> l \in S.

Lemma component_sub S (k l : edge G) : closed S -> k \in S ->
  nth false (component (bits F) (val k)) (val l) -> l \in S.
Proof.
move=> clS kS; rewrite /component; have : forall n, nth false (iter n (grow (bits F))
    (mkseq (pred1 (val k)) 45)) (val l) -> l \in S; last exact.
move=> n; elim: n l => [|n IH] l.
  by rewrite nth_mkseq ?(ltn_ord (l : 'I_45)) // => /eqP/val_inj->.
rewrite iterS nth_grow nth_bits => /andP[lF /hasP[m ml mK]].
have m_k := adjacent_lt ml; apply: (clS (Ordinal m_k)) => //; first exact: IH.
by rewrite adjacent_sym.
Qed.

Definition comps : seq (nat * seq bool) := components 6 (bits F) (nseq 45 false).

Lemma compsP : three_odd_components (bits F).
Proof. exact: (allP check_factors) (mem_factors tF). Qed.

Section Circuit.

Variable C : {set edge G}.
Hypotheses (CF : C \subset F) (cC : is_circuit C).

Lemma circuit_closed : closed C.
Proof.
move=> k l kC lF /mem_adjacent[v [kv lv]]; have [_ reg _] := cC.
have deg2 : mdeg_in C v = mdeg_in F v.
  rewrite tF; case: (reg v) => //; rewrite degreeE => /eqP.
  by rewrite -leqn0 leqNgt -has_count => /hasP[]; exists (val k); rewrite // nth_bits.
have sub : subpred (nth false (bits C)) (nth false (bits F)).
  move=> m; case: (ltnP m 45) => [m45|m45]; last by rewrite nth_default ?size_bits.
  by rewrite !(nth_bits _ (Ordinal m45)); apply: (subsetP CF).
rewrite !degreeE in deg2; rewrite -nth_bits -(count_eq sub deg2) //.
by rewrite nth_bits.
Qed.

Lemma circuit_compl : closed (F :\: C).
Proof.
move=> k l; rewrite !inE => /andP[kC kF] lF; rewrite lF andbT adjacent_sym => kl.
by apply: contra kC => lC; apply: circuit_closed lC kF kl.
Qed.

(** A circuit which meets a component is equal to it. *)
Lemma circuit_comp p (e : edge G) : p \in comps -> e \in C -> nth false p.2 (val e) ->
  forall l : edge G, (l \in C) = nth false p.2 (val l).
Proof.
move=> p_in eC pe.
have /and4P[/allP/(_ p p_in)/and4P[p1 _ /eqP grow_p _] _ _ _] := compsP.
have p45 : p.1 < 45.
  by rewrite ltnNge; apply: contraL p1 => ?; rewrite nth_default ?size_bits.
pose k : edge G := Ordinal p45; have pE : p.2 = component (bits F) (val k) := componentsP p_in.
have kF : k \in F by rewrite -nth_bits.
have kC : k \in C.
  apply: contraLR eC => kC; have /setDP[] // : e \in F :\: C.
  by apply: (component_sub circuit_compl (k := k)); rewrite -?pE // !inE kC.
have p_closed (l m : edge G) : nth false p.2 (val l) -> m \in F -> val m \in adjacent l ->
    nth false p.2 (val m).
  move=> pl mF lm; rewrite -grow_p nth_grow nth_bits mF; apply/hasP.
  by exists (val l); rewrite // -adjacent_sym.
move=> l; apply/idP/idP => [lC|]; last by rewrite pE; apply: component_sub circuit_closed kC.
pose touches (x : G) := exists2 m : edge G, nth false p.2 (val m) & val m \in star x.
have end_touches (m : edge G) x : m \in C -> touches x -> val m \in star x -> nth false p.2 (val m).
  move=> mC [m' pm' m'x] mx; apply: (p_closed m') => //; first exact: (subsetP CF).
  by apply/mem_adjacent; exists x.
have walk_touches w : forall x y : G, uwalk_in C x y w -> touches x -> touches y.
  elim: w => [|m w IH] x y /andP[]; first by move=> /eqP->.
  move=> /orP[] /andP[/eqP mx xy] /andP[mC wC] tx;
    (apply: (IH _ _ (introT andP (conj xy wC))); exists m; [|by rewrite mem_star eqxx ?orbT]);
    by apply: end_touches tx _; rewrite // mem_star mx eqxx ?orbT.
have [_ _ conn] := cC; have inc (m : edge G) : m \in C -> subgraph_incident C (source m).
  by move=> mC; apply/existsP; exists m; rewrite mC; apply/existsP; exists false.
have [w /walk_touches] := conn _ _ (inc _ eC) (inc _ lC).
move=> tl; apply: end_touches lC (tl _) _; last by rewrite mem_star eqxx.
by exists e; rewrite // mem_star eqxx.
Qed.

Lemma circuit_odd : odd #|C|.
Proof.
have [/set0Pn[e eC] _ _] := cC; have /and4P[/allP odd_p /allP cover _ _] := compsP.
have e_in : val e \in iota 0 45 by rewrite mem_iota (ltn_ord (e : 'I_45)).
have /implyP := cover _ e_in; rewrite nth_bits => /(_ (subsetP CF e eC))/hasP[p p_in pe].
have /and4P[_ _ /eqP grow_p] := odd_p p p_in.
have size_p : size p.2 = 45 by rewrite -grow_p size_map size_iota.
congr odd; rewrite -{1}(mkseq_nth false p.2) size_p count_map -(card_ord_pred 45 (nth false p.2)).
by apply: eq_card => l; rewrite inE (circuit_comp p_in eC pe).
Qed.

End Circuit.

(** In a decomposition of [F] into cycles, each component is a cycle of the decomposition. *)
Lemma not_oddness D : cycle_decomposition_of F D ->
  2 < count (fun C : {set edge G} => odd #|C|) D.
Proof.
move=> [circ mult]; have DF C : C \in D -> C \subset F.
  move=> CD; apply/subsetP => e eC; have := mult e; case: (e \in F) => // /eqP.
  by rewrite -leqn0 leqNgt -has_count => /hasP[]; exists C.
have cyc p : p \in comps -> exists (C : {set edge G}) (k : edge G),
    [/\ C \in D, val k = p.1, k \in C & forall l : edge G, (l \in C) = nth false p.2 (val l)].
  move=> p_in; have /and4P[/allP/(_ p p_in)/and4P[p1 pp _ _] _ _ _] := compsP.
  have p45 : p.1 < 45.
    by rewrite ltnNge; apply: contraL p1 => ?; rewrite nth_default ?size_bits.
  pose k : edge G := Ordinal p45; have kF : k \in F by rewrite -nth_bits.
  have /hasP[C CD kC] : has (fun C : {set edge G} => k \in C) D by rewrite has_count mult kF.
  by exists C, k; split=> //; apply: (circuit_comp (DF C CD) (circ C CD) p_in kC).
have neq (p q : nat * seq bool) (P Q : {set edge G}) (k : edge G) : val k = q.1 -> k \in Q ->
    (forall l : edge G, (l \in P) = nth false p.2 (val l)) -> ~~ nth false p.2 q.1 -> P != Q.
  by move=> kq kQ PE pq; apply: contraNneq pq => PQ; rewrite -kq -PE PQ.
have [_ _ + +] := and4P compsP; rewrite -/comps.
case: comps cyc => [|p [|q [|r s]]] // cyc /= /and3P[/and3P[pq pr _] /andP[qr _] _] _.
have [|P [kp [PD _ _ PE]]] := cyc p; first by rewrite inE eqxx.
have [|Q [kq [QD kqq kqQ QE]]] := cyc q; first by rewrite !inE eqxx orbT.
have [|R [kr [RD krr krR _]]] := cyc r; first by rewrite !inE eqxx !orbT.
rewrite -size_filter; apply: (@uniq_leq_size _ [:: P; Q; R]).
  by rewrite /= !inE negb_or (neq p q _ _ kq) // (neq p r _ _ kr) // (neq q r _ _ kr).
by move=> C; rewrite !inE mem_filter => /or3P[] /eqP->; rewrite circuit_odd ?DF //; apply: circ.
Qed.

End TwoFactor.

(** ** Connectivity and bridges *)

Lemma loopless : mloopless G.
Proof. by move=> e; case/andP: (ends_lt e) => _; rewrite -sourceE -targetE val_eqE. Qed.

Lemma cubic : mcubic G.
Proof.
move=> v; have -> : #|edges_at v| = #|[set k : 'I_45 | val k \in star v]|.
  apply: eq_card => k; rewrite !inE mem_star.
  by apply/existsP/orP => [[[] ->]|[] kv]; [right|left|exists false|exists true].
rewrite (card_ord_pred _ (mem (star v))); apply/eqP.
exact: (ord_all v (P := fun v => count (mem (star v)) (iota 0 45) == 3)).
Qed.

Lemma skeleton_edge (e : edge G) : (source e : skeleton.skeleton G) -- target e.
Proof.
apply/andP; split; first exact: loopless.
by apply/existsP; exists e; rewrite !inE !eqxx.
Qed.

(** Every vertex but 0 is adjacent to a smaller one. *)
Lemma connected_G : connected [set: skeleton.skeleton G].
Proof.
have sym : connect_sym (@edge_rel (skeleton.skeleton G)) by apply/connect_symI/sg_sym.
pose o : skeleton.skeleton G := ord0 : 'I_30; suff to0 v : connect (--) o v.
  by apply: connectedTI => x y; apply: connect_trans (to0 y); rewrite sym.
have [n] := ubnP (val v); elim: n v => // n IH v; rewrite ltnS => vn.
have := ord_all v (P := fun v => (v == 0) || has (fun k =>
  ((ends k).1 == v) && ((ends k).2 < v) || ((ends k).2 == v) && ((ends k).1 < v)) (iota 0 45)) isT.
case/predU1P=> [v0|/hasP[k]]; first by rewrite (_ : v = o) //; apply: val_inj.
rewrite mem_iota => k45; pose e : edge G := Ordinal k45.
rewrite -(sourceE e) -(targetE e) !val_eqE.
have e1 := connect1 (skeleton_edge e); have e2 := e1; rewrite sym in e2.
by move=> /orP[]/andP[/eqP ve lt]; rewrite -ve; [apply: connect_trans e2|apply: connect_trans e1];
  apply: IH; apply: leq_trans vn.
Qed.

(** A walk between the ends of each edge that avoids this edge: the rest of a cycle of its copy, or
    a path around the ring for a joining edge. *)
Definition bypass (k : nat) : seq nat := [seq (l + 15 * (k %/ 15)) %% 45 | l <-
  nth [::] [:: [:: 1; 4; 8; 3]; [:: 0; 2; 6; 5]; [:: 0; 1; 5; 6]; [:: 0; 1; 4; 8]; [:: 1; 0; 3; 8];
               [:: 1; 0; 2; 6]; [:: 2; 0; 1; 5]; [:: 2; 3; 8; 10]; [:: 3; 0; 1; 4];
               [:: 3; 2; 6; 11]; [:: 4; 5; 6; 7]; [:: 5; 4; 8; 9]; [:: 7; 6; 11; 13];
               [:: 9; 8; 10; 12]; [:: 12; 7; 2; 0; 44; 42; 37; 32; 30; 29; 27; 22; 17; 15]]
      (k %% 15)].

Fixpoint walk (x y : nat) (w : seq nat) : bool :=
  if w is k :: w' then
    if (ends k).1 == x then walk (ends k).2 y w' else ((ends k).2 == x) && walk (ends k).1 y w'
  else x == y.

Lemma walk_uwalk (w : seq (edge G)) (x y : G) : walk (val x) (val y) (map val w) -> uwalk x y w.
Proof.
elim: w x => [|k w IH] x; first by rewrite /= val_eqE.
have -> : walk (val x) (val y) (map val (k :: w)) =
    if source k == x then walk (val (target k)) (val y) (map val w)
    else (target k == x) && walk (val (source k)) (val y) (map val w).
  by rewrite -!val_eqE !sourceE !targetE.
by case: ifP => [sx /IH|_ /andP[tx /IH]] w_w; apply/orP; [left|right]; apply/andP.
Qed.

Lemma no_bridge : bridgeless G.
Proof.
move=> e bridge; pose w : seq 'I_45 := map inord (bypass e).
have /and3P[/allP lt45 e_w walk_w] := ord_all e (P := fun k =>
  [&& all (gtn 45) (bypass k), k \notin bypass k & walk (ends k).1 (ends k).2 (bypass k)]) isT.
have w_val : map val w = bypass e.
  by rewrite -map_comp -[RHS]map_id; apply/eq_in_map => l /lt45 ?; rewrite /= inordK.
have : e \in w by apply/bridge/walk_uwalk; rewrite w_val sourceE targetE.
by move/(map_f val); rewrite w_val (negPf e_w).
Qed.

Theorem disproof : ~ OPG_cubic_odd_2_factors_oddness_2.
Proof.
move=> /(_ G) []; first by rewrite card_ord.
- exact: conj loopless cubic.
- exact: connected_G.
- exact: no_bridge.
- by move=> F tF C CF cC; exact (circuit_odd tF CF cC).
by move=> F [D [tF dec]]; rewrite leqNgt (not_oddness tF dec).
Qed.
