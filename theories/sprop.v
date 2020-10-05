From Coq Require Export Logic.StrictProp.
From stdpp Require Import base decidable.
From stdpp Require Import options.

Definition is_true (b: bool): SProp := if b then sUnit else sEmpty.

Lemma is_true_intro {b: bool} : Is_true b → is_true b.
Proof.
  destruct b; simpl; [ constructor | intros [] ].
Defined.

Lemma is_true_elim {b: bool} : is_true b → Is_true b.
Proof.
  destruct b; simpl; [constructor | intros []].
Defined.

Lemma is_true_fmap {P Q: bool} (lem: P → Q) : is_true P → is_true Q.
Proof.
  destruct Q; simpl; [ constructor | ].
  intros.
  destruct P; [ | exact H ].
  exfalso. apply (lem I).
Defined.

Lemma is_true_bind {P Q: bool} (HP: is_true P) (lem: P → is_true Q) : is_true Q.
Proof.
  destruct Q; simpl; [ constructor | ].
  apply (lem (is_true_elim HP)).
Defined.

Definition sprop_decide (P: Prop) {dec: Decision P} : SProp :=
  is_true (bool_decide P).

Lemma sprop_decide_pack (P: Prop) {dec: Decision P} : P → sprop_decide P.
Proof.
  intros H.
  apply is_true_intro; auto using bool_decide_pack.
Qed.
Lemma sprop_decide_unpack (P: Prop) {dec: Decision P} : sprop_decide P → P.
Proof.
  intros H%is_true_elim.
  eapply bool_decide_unpack; auto.
Qed.

(* currently unused; partial progress towards getting coPset to use SProp's Ssig
rather than sig (with a proof in Prop) *)
Definition proj1_Ssig {A:Type} {P:A → SProp} (e: Ssig P) : A :=
  let (a, _) := e in a.
Definition proj2_Ssig {A:Type} {P:A → SProp} (e: Ssig P) : P (proj1_Ssig e) :=
  let (_, H) := e in H.
Lemma Ssig_eq_pi {A:Type} {P:A → SProp}
      (x y: Ssig P) : x = y ↔ proj1_Ssig x = proj1_Ssig y.
Proof.
  split; [intros ->; auto |].
  destruct x, y; simpl; intros ->; auto.
Qed.
(* named after eq_sig_hprop *)
Lemma eq_Ssig {A:Type} {P:A → SProp}
      (x y: Ssig P) : proj1_Ssig x = proj1_Ssig y → x = y.
Proof. apply Ssig_eq_pi. Qed.

Global Instance Ssig_eq_dec {A:Type} {dec: EqDecision A} {P: A → SProp} : EqDecision (Ssig P).
Proof.
  intros x y.
  destruct (decide (proj1_Ssig x = proj1_Ssig y)); [left|right].
  - apply eq_Ssig; auto.
  - abstract (intros ->; contradiction).
Defined.
