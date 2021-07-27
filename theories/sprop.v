From Coq Require Export Logic.StrictProp.
From stdpp Require Import decidable.
From stdpp Require Import options.

Lemma unsquash (P : Prop) `{!Decision P} : Squash P → P.
Proof.
  intros HP. destruct (decide P) as [?|HnotP]; [assumption|].
  assert sEmpty as []. destruct HP. destruct HnotP; assumption.
Qed.

Definition SIs_true (b : bool) : SProp := Squash (Is_true b).

Lemma SIs_true_intro b : Is_true b → SIs_true b.
Proof. apply squash. Qed.
Lemma SIs_true_elim b : SIs_true b → Is_true b.
Proof. apply (unsquash _). Qed.
