From Coq Require Export Logic.StrictProp.
From stdpp Require Import decidable.
From stdpp Require Import options.

Definition SIs_true (b: bool): SProp := if b then sUnit else sEmpty.

Lemma SIs_true_intro {b: bool} : Is_true b → SIs_true b.
Proof. destruct b; [constructor | intros []]. Qed.
Lemma SIs_true_elim {b: bool} : SIs_true b → Is_true b.
Proof. destruct b; simpl; [constructor | intros []]. Qed.

Definition sprop_decide (P : Prop) `{!Decision P} : SProp :=
  SIs_true (bool_decide P).

Lemma sprop_decide_pack (P : Prop) `{!Decision P} : P → sprop_decide P.
Proof. intros HP. apply SIs_true_intro, bool_decide_pack, HP. Qed.
Lemma sprop_decide_unpack (P : Prop) `{!Decision P} : sprop_decide P → P.
Proof. intros HP. apply (bool_decide_unpack P), SIs_true_elim, HP. Qed.
