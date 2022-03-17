From stdpp Require Import tactics telescopes.

Local Unset Mangle Names. (* for stable goal printing *)

Section accessor.
(* This is like Iris' accessors, but in Prop.  Just to play with telescopes. *)
Definition accessor {X : tele} (α β γ : X → Prop) : Prop :=
  ∃.. x, α x ∧ (β x → γ x).

(* Working with abstract telescopes. *)
Section tests.
Context {X : tele}.
Implicit Types α β γ : X → Prop.

Lemma acc_mono α β γ1 γ2 :
  (∀.. x, γ1 x → γ2 x) →
  accessor α β γ1 → accessor α β γ2.
Proof.
  unfold accessor. rewrite tforall_forall, !texist_exist.
  intros Hγ12 Hacc. destruct Hacc as [x' [Hα Hclose]]. exists x'.
  split; [done|]. intros Hβ. apply Hγ12, Hclose. done.
Qed.

Lemma acc_mono_disj α β γ1 γ2 :
  accessor α β γ1 → accessor α β (λ.. x, γ1 x ∨ γ2 x).
Proof.
  Show.
  apply acc_mono. Show.
  rewrite tforall_forall. intros x Hγ. rewrite tele_app_bind. Show.
  left. done.
Qed.
End tests.
End accessor.

(* Type inference for tele_app-based notation.
(Relies on [&] bidirectionality hint of tele_app.) *)
Definition test {TT : tele} (t : TT → Prop) : Prop :=
  ∀.. x, t x ∧ t x.
Notation "'[TEST'  x .. z ,  P ']'" :=
  (test (TT:=(TeleS (fun x => .. (TeleS (fun z => TeleO)) ..)))
        (tele_app (λ x, .. (λ z, P) ..)))
  (x binder, z binder).
Check [TEST (x y : nat), x = y].

(** [tele_arg t] should live at the same universe
as the types inside of [t] because [tele_arg t]
is essentially just a (dependent) product.
 *)
Definition no_bump@{u} (t : tele@{u}) : Type@{u} := tele_arg@{u} t.

Lemma texist_exist_universes (X : Type) (P : TeleS (fun _ : X => TeleO) -> Prop) :
  texist P <-> ex P.
Proof. by rewrite texist_exist. Qed.
