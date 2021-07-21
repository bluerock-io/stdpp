From stdpp Require Import namespaces strings.

Section tests.
Implicit Types (N : namespace) (E : coPset).

Lemma test1 N1 N2 :
  N1 ## N2 → ↑N1 ⊆@{coPset} ⊤ ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test2 N1 N2 :
  N1 ## N2 → ↑N1.@"x" ⊆@{coPset} ⊤ ∖ ↑N1.@"y" ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test3 N :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x".
Proof. solve_ndisj. Qed.

Lemma test4 N :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x" ∖ ↑N.@"y".
Proof. solve_ndisj. Qed.

Lemma test5 N1 N2 :
  ⊤ ∖ ↑N1 ∖ ↑N2 ⊆@{coPset} ⊤ ∖ ↑N1.@"x" ∖ ↑N2 ∖ ↑N1.@"y".
Proof. solve_ndisj. Qed.

Lemma test_ndisjoint_difference_l N : ⊤ ∖ ↑N ##@{coPset} ↑N.
Proof. solve_ndisj. Qed.
Lemma test_ndisjoint_difference_r N : ↑N ##@{coPset} ⊤ ∖ ↑N.
Proof. solve_ndisj. Qed.

Lemma test6 E N :
  ↑N ⊆ E → ↑N ⊆ ⊤ ∖ (E ∖ ↑N).
Proof. solve_ndisj. Qed.

Lemma test7 N :
  ↑N ⊆@{coPset} ⊤ ∖ ∅.
Proof. solve_ndisj. Qed.

Lemma test8 N1 N2 :
  ⊤ ∖ (↑N1 ∪ ↑N2) ⊆@{coPset} ⊤ ∖ ↑N1.@"counter".
Proof. solve_ndisj. Qed.

Lemma test9 N1 N2 :
  ⊤ ∖ (↑N1 ∪ ↑N2) ⊆@{coPset} ⊤ ∖ ↑N1.@"counter" ∖ ↑N1.@"state" ∖ ↑N2.
Proof. solve_ndisj. Qed.
