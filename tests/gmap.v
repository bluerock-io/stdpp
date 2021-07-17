From stdpp Require Import gmap.

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

Goal 1 ∈ dom (M := gmap _ _) (gset _) (<[ 1 := 2 ]> ∅).
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal bool_decide (∅ =@{gset _} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ≡@{gset _} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (1 ∈@{gset _} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ##@{gset _} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ⊆@{gset _} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.
