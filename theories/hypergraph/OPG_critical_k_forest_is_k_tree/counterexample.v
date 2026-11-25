(** * A critical 3-forest that is not tight

The hypergraph E on {0, ..., 5} has the edges 012, 023, 034, 124, 125, 145, 234 and 345.

It is a 3-forest: a colouring is given for each edge [witnesses].  It is critical: if e is another
set of three vertices, then e has three colours in every colouring where f is the only edge with
three colours, for f = 124 or f = 234 [saturated]; this is checked on the 3^6 colourings.  It is
not tight: in the colouring with classes {1}, {3} and {0, 2, 4, 5}, no edge has three colours,
since no edge contains 1 and 3.

The conjecture was disproved by Gebauer, Gundert, Moser and Okamoto (arXiv:1109.3390).  The
counterexample given here was found by computer search. *)

From GC.hypergraph.OPG_critical_k_forest_is_k_tree Require main.
From mathcomp Require Import boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation all_colors := main.all_colors.

(** Vertices and colours are represented by numbers, and colourings by lists. *)
Definition edges : seq (seq nat) :=
  [:: [:: 0; 1; 2]; [:: 0; 2; 3]; [:: 0; 3; 4]; [:: 1; 2; 4];
      [:: 1; 2; 5]; [:: 1; 4; 5]; [:: 2; 3; 4]; [:: 3; 4; 5]].

Definition vset (s : seq nat) : {set 'I_6} := [set v : 'I_6 | val v \in s].

Definition E : {set {set 'I_6}} := [set e in map vset edges].

Definition triple (s : seq nat) : bool := [&& uniq s, size s == 3 & all (gtn 6) s].

Definition colors (c s : seq nat) : bool := uniq [seq nth 0 c v | v <- s].

Definition table (col : 'I_6 -> 'I_3) : seq nat := [seq val (col v) | v <- enum 'I_6].

(** The lists of [k] numbers smaller than [n]. *)
Fixpoint words (n k : nat) : seq (seq nat) :=
  if k is k'.+1 then [seq x :: s | x <- iota 0 n, s <- words n k'] else [:: [::]].

Lemma mem_words n s : all (gtn n) s -> s \in words n (size s).
Proof.
elim: s => //= x s IH /andP[xn /IH s_in]; apply/allpairsP; exists (x, s).
by rewrite mem_iota.
Qed.

Lemma tableP col : table col \in words 3 6.
Proof.
have -> : 6 = size (table col) by rewrite size_map size_enum_ord.
by apply: mem_words; apply/allP => _ /mapP[v _ ->] /=.
Qed.

Lemma triple_inord s v : triple s -> v \in s -> val (inord v : 'I_6) = v.
Proof. by case/and3P=> _ _ /allP s6 /s6 v6; rewrite /= inordK. Qed.

Lemma eq_vset s t : triple s -> triple t -> (vset s == vset t) = perm_eq s t.
Proof.
move=> ts tt; have [us _ _] := and3P ts; have [ut _ _] := and3P tt.
apply/eqP/idP => [st|/perm_mem st]; last by apply/setP => v; rewrite !inE st.
apply: uniq_perm => // x; apply/idP/idP => xs.
  by have /setP/(_ (inord x)) := st; rewrite !inE (triple_inord ts xs) xs => <-.
by have /setP/(_ (inord x)) := st; rewrite !inE (triple_inord tt xs) xs => ->.
Qed.

Lemma vset_enum (e : {set 'I_6}) : vset (map val (enum e)) = e.
Proof. by apply/setP => v; rewrite inE (mem_map val_inj) mem_enum. Qed.

Lemma triple_enum (e : {set 'I_6}) : triple (map val (enum e)) = (#|e| == 3).
Proof.
rewrite /triple (map_inj_uniq val_inj) enum_uniq.
rewrite size_map -cardE all_map /=; apply: andb_idr => _.
by apply/allP => v _; apply: ltn_ord.
Qed.

Lemma card_vset s : triple s -> #|vset s| = 3.
Proof.
move=> ts; have [us /eqP sz _] := and3P ts.
rewrite -[RHS]sz -(size_map (inord : nat -> 'I_6)).
have /card_uniqP<- : uniq (map (inord : nat -> 'I_6) s).
  by rewrite map_inj_in_uniq // => x y xs ys /(congr1 val); rewrite !(triple_inord ts).
apply: eq_card => v; rewrite inE; apply/idP/mapP => [vs|[x xs ->]].
  by exists (val v) => //; apply: val_inj; rewrite (triple_inord ts).
by rewrite (triple_inord ts).
Qed.

Lemma all_colorsE col s : triple s -> all_colors col (vset s) = colors (table col) s.
Proof.
case/and3P=> us /eqP sz /allP s6.
have tE (v : 'I_6) : nth 0 (table col) v = col v.
  by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum.
apply/forallP/idP => [all_c|uc i].
  apply: (@leq_size_uniq _ (iota 0 3)); rewrite ?iota_uniq ?size_map ?sz ?size_iota //.
  move=> i; rewrite mem_iota /= => i3; have /exists_inP[v] := all_c (Ordinal i3).
  by rewrite inE => vs /eqP cv; apply/mapP; exists (val v); rewrite // tE cv.
have [||_ /(_ i)] := uniq_min_size uc (s2 := iota 0 3).
- move=> _ /mapP[v /s6 v6 ->]; rewrite mem_iota /=.
  by rewrite (tE (Ordinal v6)).
- by rewrite size_map sz.
rewrite mem_iota /= ltn_ord => /mapP[v vs iv]; apply/exists_inP.
have v6 := s6 _ vs; exists (Ordinal v6); first by rewrite inE.
by apply/eqP/val_inj; rewrite /= iv -(tE (Ordinal v6)).
Qed.

Lemma edges_triple : all triple edges.
Proof. by []. Qed.

(** Among the triples [es], the colouring [c] has three colours on [f] only. *)
Definition only (f : seq nat) (es : seq (seq nat)) (c : seq nat) : bool :=
  all (fun s => colors c s == perm_eq s f) es.

Lemma only_vset f es col : triple f -> all triple es ->
  (forall e, e \in map vset es -> (all_colors col e <-> e = vset f)) <-> only f es (table col).
Proof.
move=> tf /allP tes; split=> [ok|/allP ok _ /mapP[s ses ->]].
  apply/allP => s ses; rewrite -(all_colorsE _ (tes _ ses)) -(eq_vset (tes _ ses) tf).
  by apply/eqP; apply/idP/eqP => /(ok _ (map_f vset ses)).
rewrite (all_colorsE _ (tes _ ses)) (eqP (ok _ ses)) -(eq_vset (tes _ ses) tf).
by split=> /eqP.
Qed.

Definition coloring (c : seq nat) (v : 'I_6) : 'I_3 := inord (nth 0 c v).

Lemma coloringK c : size c = 6 -> all (gtn 3) c -> table (coloring c) = c.
Proof.
move=> sz /allP c3; apply: (@eq_from_nth _ 0); rewrite size_map size_enum_ord // => i i6.
rewrite (nth_map ord0) ?size_enum_ord //= inordK ?nth_enum_ord //.
by apply: c3; rewrite mem_nth ?sz.
Qed.

Definition witnesses : seq (seq nat) :=
  [:: [:: 0; 1; 2; 0; 2; 2]; [:: 0; 1; 1; 2; 2; 1]; [:: 0; 1; 1; 1; 2; 1]; [:: 0; 1; 0; 2; 2; 1];
      [:: 0; 0; 1; 0; 0; 2]; [:: 0; 0; 0; 1; 1; 2]; [:: 0; 1; 1; 0; 2; 2]; [:: 0; 0; 0; 1; 0; 2]].

Lemma witnessesP : all (fun f =>
  has (fun c => [&& size c == 6, all (gtn 3) c & only f edges c]) witnesses) edges.
Proof. by []. Qed.

Lemma k_forest_E : main.k_forest 3 E.
Proof.
split=> e; rewrite inE => /mapP[f f_in ->]; have tf := allP edges_triple f f_in.
  exact: card_vset.
have /hasP[c _ /and3P[/eqP sz c3 ok]] := allP witnessesP f f_in.
exists (coloring c) => g; rewrite inE; apply: (only_vset _ tf edges_triple).2.
by rewrite coloringK.
Qed.

(** The colourings where [f] is the only edge with three colours. *)
Definition colorings (f : seq nat) : seq (seq nat) := [seq c <- words 3 6 | only f edges c].

(** No set of three vertices can be added to the edges: it has three colours in all the colourings
    associated with the edge 124, or in all those associated with the edge 234. *)
Lemma saturated : let cs := colorings [:: 1; 2; 4] in let cs' := colorings [:: 2; 3; 4] in
  all (fun s => [|| ~~ triple s, has (perm_eq s) edges, all (colors^~ s) cs | all (colors^~ s) cs'])
    (words 6 3).
Proof. by vm_compute. Qed.

Lemma critical_E : main.critical_k_forest 3 E.
Proof.
split=> [|e e3 eE]; first exact: k_forest_E.
have ts : triple (map val (enum e)) by rewrite triple_enum e3.
rewrite -(vset_enum e) in eE *; move: (map val (enum e)) ts eE => s ts eE [_ forest].
have [_ /eqP sz s6] := and3P ts; have s_in := mem_words s6; rewrite sz in s_in.
have nE : ~~ has (perm_eq s) edges.
  apply: contra eE => /hasP[f f_in]; rewrite -(eq_vset ts (allP edges_triple f f_in)) => /eqP->.
  by rewrite inE map_f.
have [f f_in /allP f_s] : exists2 f, f \in edges & all (colors^~ s) (colorings f).
  have := allP saturated s s_in; rewrite ts (negPf nE) /=.
  by case/orP; [exists [:: 1; 2; 4] | exists [:: 2; 3; 4]].
have [|col ok] := forest (vset f); first by rewrite in_setU1 [_ \in E]inE map_f ?orbT.
have only_f : only f (s :: edges) (table col).
  apply/only_vset; [exact: allP edges_triple f f_in | by apply/andP |].
  by move=> g /predU1P g_in; apply: ok; rewrite in_setU1 inE; apply/predU1P.
have [/eqP s_f only_E] : _ /\ only f edges (table col) := andP only_f.
case/hasP: nE; exists f => //; rewrite -s_f; apply: f_s.
by rewrite mem_filter only_E tableP.
Qed.

Lemma not_tight : ~ main.hg_tight 3 E.
Proof.
move=> tight; pose c := [:: 0; 1; 0; 2; 0; 0].
have [|e] := tight (coloring c).
  move=> i; exists (inord (nth 0 [:: 0; 1; 3] i)); apply: val_inj.
  by case: i => -[|[|[|]]] //= _; rewrite !inordK.
have /allP no : all (fun f => ~~ colors c f) edges by [].
rewrite inE => /mapP[f f_in ->]; rewrite (all_colorsE _ (allP edges_triple f f_in)) coloringK //.
by apply/negP/no.
Qed.

Theorem disproof : ~ main.OPG_critical_k_forest_is_k_tree.
Proof. by move=> /(_ 3 _ E critical_E)[_ /not_tight]. Qed.
