From stdpp Require Import tactics option.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  P1 ∨ (Is_true (P2 || P3)) ∨ P4 →
  (P1 → P) →
  (P2 → P) →
  (P3 → P) →
  (P4 → P) →
  P.
Proof.
  intros * HH X1 X2 X3 X4.
  destruct_or? HH; [ exact (X1 HH) | exact (X2 HH) | exact (X3 HH) | exact (X4 HH) ].
Qed.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  P1 ∨ P2 →
  P3 ∨ P4 →
  (P1 → P3 → P) →
  (P1 → P4 → P) →
  (P2 → P3 → P) →
  (P2 → P4 → P) →
  P.
Proof.
  intros * HH1 HH2 X1 X2 X3 X4.
  destruct_or?; [ exact (X1 HH1 HH2) | exact (X3 HH1 HH2) | exact (X2 HH1 HH2) | exact (X4 HH1 HH2) ].
Qed.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  id (P1 ∨ P2) →
  id (P3 ∨ P4) →
  (P1 → P3 → P) →
  (P1 → P4 → P) →
  (P2 → P3 → P) →
  (P2 → P4 → P) →
  P.
Proof.
  intros * HH1 HH2 X1 X2 X3 X4.
  Fail progress destruct_or?.
  Fail progress destruct_or!.
  destruct_or! HH1; destruct_or! HH2;
  [ exact (X1 HH1 HH2) | exact (X2 HH1 HH2) | exact (X3 HH1 HH2) | exact (X4 HH1 HH2) ].
Qed.

Goal ∀ P1 P2 P3 P4,
  P1 ∧ (Is_true (P2 && P3)) ∧ P4 →
  P1 ∧ P2 ∧ P3.
Proof.
  intros * HH. split_and!; [ destruct_and? HH; assumption | destruct_and?; assumption | ].
  destruct_and?. Fail destruct_and!. assumption.
Qed.

(** Tests for [case_match] *)
Goal ∀ n : nat, match n with | 0 => n = 0 | S n' => n = S n' end.
Proof.
  intros. by case_match.
Restart.
  intros. by case_match eqn:Heq; revert Heq. (* [revert Heq] checks that [Heq] exists *)
Qed.

Goal ∀ n m : nat, match n with | 0 => m = 0 | S n' => m = S n' end → n = m.
Proof.
  intros. by case_match.
Restart.
  intros. by case_match eqn:Heq; revert Heq. (* [revert Heq] checks that [Heq] exists *)
Qed.

(** Tests for [select] tactics *)
Goal ∀ (n : nat), ∃ m : nat, True.
Proof. intros ?. rename select nat into m. exists m. done. Qed.

Goal ∀ (P : nat → Prop), P 3 → P 4 → P 4.
Proof. intros P **. rename select (P _) into HP4. apply HP4. Qed.

Goal ∀ P Q : Prop, True ∨ True → P ∨ Q → Q ∨ P.
Proof.
  intros P Q ??. (* should select the last hypothesis *)
  destruct select (_ ∨ _); by constructor.
Restart.
  intros P Q ??. (* should select the last hypothesis *)
  destruct select (_ ∨ _) as [H1|H2].
  - right. exact H1.
  - left. exact H2.
Qed.

(** Regression tests for [naive_solver]. *)
Lemma naive_solver_issue_115 (P : nat → Prop) (x : nat) :
  (∀ x', P x' → x' = 10) → P x → x + 1 = 11.
Proof. naive_solver. Qed.

(** [mk_evar] works on things that coerce to types. *)
(** This is a feature when we have packed structures, for example Iris's [ofe]
(fields other than the carrier omitted). *)
Structure ofe := Ofe { ofe_car :> Type }.
Goal ∀ A : ofe, True.
intros A.
let x := mk_evar A in idtac.
Abort.
(** More surprisingly, it also works for other coercions into a
universe, like [Is_true : bool → Prop]. *)
Goal True.
let x := mk_evar true in idtac.
Abort.

(** Make sure that [done] is not called recursively when solving [is_Some],
which might leave an unresolved evar before performing ex falso. *)
Goal False → is_Some (@None nat).
Proof. done. Qed.
Goal ∀ mx, mx = Some 10 → is_Some mx.
Proof. done. Qed.
Goal ∀ mx, Some 10 = mx → is_Some mx.
Proof. done. Qed.

(** get_head tests. *)
Lemma test_get_head (f : nat → nat → nat → nat) : True.
Proof.
  let f' := get_head (f 0 1 2) in unify f f'.
  let f' := get_head f in unify f f'.
Abort.
