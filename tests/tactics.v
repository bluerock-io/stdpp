From stdpp Require Import tactics option strings.

Local Unset Mangle Names. (* for stable goal printing *)

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

(** (e)feed tests *)
Lemma feed1 (P Q R : Prop) :
  P → Q → (P → Q → R) → R.
Proof.
  intros HP HQ HR.
  feed specialize HR; [exact HP|exact HQ|exact HR].
Restart.
  intros HP HQ HR.
  feed pose proof HR as HR'; [exact HP|exact HQ|exact HR'].
Qed.
Lemma efeed1 (P Q R : nat → Prop) :
  P 1 → Q 1 → (∀ n, P n → Q n → R n) → R 1.
Proof.
  intros HP HQ HR.
  Fail progress feed specialize HR.
  efeed specialize HR; [exact HP|exact HQ|exact HR].
Restart.
  intros HP HQ HR.
  efeed pose proof HR as HR'; [exact HP|exact HQ|exact HR'].
Qed.

(** o-tactic tests *)
Check "otest".
Lemma otest (P Q R : nat → Prop) :
  (∀ m n, P n → Q m → R (n + m)) →
  (∀ m n, P n → Q m → R (n + m) ∧ R 2) →
  P 0 → P 1 → Q 5 → R 6.
Proof.
  intros HPQR1 HPQR2 HP0 HP1 HQ.
  (** Imagine we couldn't [apply] since the goal is still very different, we
  need forward reasoning. Also we don't have proof terms for [P n] and [Q m] but
  a short proof script can solve them. [n] needs to be specified, but [m] is
  huge and we don't want to specify it. We cannot use [efeed] as that will make
  both [n] and [m] into evars. What do we do? The "o" family of tactics for
  working with "o"pen terms helps. *)
  opose proof (HPQR1 _ 1 _ _) as HR; [exact HP1|exact HQ|]. exact HR.
Undo. Undo.
  (** Same deal for [generalize]. *)
  ogeneralize (HPQR1 _ 1 _ _); [exact HP1|exact HQ|]. intros HR; exact HR.
Undo. Undo.
  (** [odestruct] also automatically adds subgoals until there is something
  to destruct, as usual. Note that [edestruct] wouldn't help here,
  it just complains that it cannot infer the placeholder. *)
  Fail edestruct (HPQR2 _ 1).
  odestruct (HPQR2 _ 1) as [HR1 HR2]; [exact HP1|exact HQ|]. exact HR1.
Undo. Undo.
  (** [ospecialize] is like [opose proof] but it reuses the name.
  It only works on local assumptions. *)
  Fail ospecialize (mk_is_Some None).
  ospecialize (HPQR1 _ 1 _ _); [exact HP1|exact HQ|]. exact HPQR1.
Qed.
