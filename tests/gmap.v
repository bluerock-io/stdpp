From stdpp Require Import pmap gmap.

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

Theorem gmap_insert_comm :
  <[3:=false]> {[2:=true]} =@{gmap nat bool} <[2:=true]> {[3:=false]}.
Proof.
  simpl. Show.
  reflexivity.
Qed.

Transparent gmap_empty.
Arguments map_insert _ _ _ / _ _ _ _ : assert.
Arguments Plookup _ _ _ / : assert.

Theorem gmap_lookup_concrete :
  lookup (M:=gmap nat bool) 2 (<[3:=false]> {[2:=true]}) = Some true.
Proof. simpl. Show. reflexivity. Qed.
