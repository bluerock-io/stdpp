From stdpp Require Import strings pmap gmap.

Goal {[1; 2; 3]} =@{gset nat} ∅.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal elements (C := gset nat) {[1; 2; 3]} = [].
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal
  {[1; 2; 3]} ∖ {[ 1 ]} ∪ {[ 4 ]} ∩ {[ 10 ]} =@{gset nat} ∅ ∖ {[ 2 ]}.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal 1 ∈ dom (M := gmap nat nat) (gset nat) (<[ 1 := 2 ]> ∅).
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal bool_decide (∅ =@{gset nat} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ≡@{gset nat} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (1 ∈@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ##@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ⊆@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Definition pmap_insert_positives (n : positive) : Pmap unit :=
  Pos.iter (λ rec p m,
    rec (p + 1)%positive (<[p:=tt]> m)) (λ _ m, m) n 1%positive ∅.
Definition pmap_insert_positives_rev (n : positive) : Pmap unit :=
  Pos.iter (λ rec p m,
    rec (p - 1)%positive (<[p:=tt]> m)) (λ _ m, m) n n ∅.

(* Test that the time is approximately n-log-n. We cannot test this on CI since
you get different timings all the time.
Definition pmap_insert_positives_test (p : positive) : bool :=
  bool_decide (pmap_insert_positives p = pmap_insert_positives_rev p).

Time Eval vm_compute in pmap_insert_positives_test 1000.
Time Eval vm_compute in pmap_insert_positives_test 2000.
Time Eval vm_compute in pmap_insert_positives_test 4000.
Time Eval vm_compute in pmap_insert_positives_test 8000.
Time Eval vm_compute in pmap_insert_positives_test 16000.
Time Eval vm_compute in pmap_insert_positives_test 32000.
Time Eval vm_compute in pmap_insert_positives_test 64000.
Time Eval vm_compute in pmap_insert_positives_test 128000.
Time Eval vm_compute in pmap_insert_positives_test 256000.
Time Eval vm_compute in pmap_insert_positives_test 512000.
Time Eval vm_compute in pmap_insert_positives_test 1000000.
*)

Definition gmap_insert_positives (n : positive) : gmap positive unit :=
  Pos.iter (λ rec p m,
    rec (p + 1)%positive (<[p:=tt]> m)) (λ _ m, m) n 1%positive ∅.
Definition gmap_insert_positives_rev (n : positive) : gmap positive unit :=
  Pos.iter (λ rec p m,
    rec (p - 1)%positive (<[p:=tt]> m)) (λ _ m, m) n n ∅.

(* Test that the time increases linearly *)
Definition gmap_insert_positives_test (p : positive) : bool :=
  bool_decide (gmap_insert_positives p = gmap_insert_positives_rev p).

(* Test that the time is approximately n-log-n. We cannot test this on CI since
you get different timings all the time.
Time Eval vm_compute in gmap_insert_positives_test 1000.
Time Eval vm_compute in gmap_insert_positives_test 2000.
Time Eval vm_compute in gmap_insert_positives_test 4000.
Time Eval vm_compute in gmap_insert_positives_test 8000.
Time Eval vm_compute in gmap_insert_positives_test 16000.
Time Eval vm_compute in gmap_insert_positives_test 32000.
Time Eval vm_compute in gmap_insert_positives_test 64000.
Time Eval vm_compute in gmap_insert_positives_test 128000.
Time Eval vm_compute in gmap_insert_positives_test 256000.
Time Eval vm_compute in gmap_insert_positives_test 512000.
Time Eval vm_compute in gmap_insert_positives_test 1000000.
*)

Check "gmap_insert_comm".
Theorem gmap_insert_comm :
  {[ 3:=false; 2:=true]} =@{gmap nat bool} {[ 2:=true; 3:=false ]}.
Proof. simpl. Show. reflexivity. Qed.

Check "gmap_lookup_concrete".
Theorem gmap_lookup_concrete :
  lookup (M:=gmap nat bool) 2 {[ 3:=false; 2:=true ]} = Some true.
Proof. simpl. Show. reflexivity. Qed.

Theorem gmap_insert_positives_reflexivity_500 :
  gmap_insert_positives 500 = gmap_insert_positives_rev 500.
Proof. reflexivity. Qed.
Theorem gmap_insert_positives_reflexivity_1000 :
  gmap_insert_positives 1000 = gmap_insert_positives_rev 1000.
Proof. (* this should take about a second *) reflexivity. Qed.

Theorem gmap_insert_positives_union_reflexivity_500 :
  (gmap_insert_positives_rev 400) ∪
    (gmap_insert_positives 500 ∖ gmap_insert_positives_rev 400)
  = gmap_insert_positives 500.
Proof. reflexivity. Qed.
Theorem gmap_insert_positives_union_reflexivity_1000 :
  (gmap_insert_positives_rev 800) ∪
    (gmap_insert_positives 1000 ∖ gmap_insert_positives_rev 800)
  = gmap_insert_positives 1000.
Proof. reflexivity. Qed.
