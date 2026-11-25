From GC.digraph.AX_digraph_strong_forward_cover_log_n Require Import main(AX_digraph_strong_forward_cover_log_n).
From GC.digraph.AX_digraph_strong_forward_cover_log_n Require diamonds.

Theorem AX_digraph_strong_forward_cover_log_n_fails : ~ AX_digraph_strong_forward_cover_log_n.
Proof. exact diamonds.no_log_forward_cover. Qed.

Check (AX_digraph_strong_forward_cover_log_n_fails :
  ~ GC.digraph.AX_digraph_strong_forward_cover_log_n.main.AX_digraph_strong_forward_cover_log_n).
Print Assumptions AX_digraph_strong_forward_cover_log_n_fails.
