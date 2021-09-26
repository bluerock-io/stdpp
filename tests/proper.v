From stdpp Require Import prelude fin_maps propset.

(** Some tests for solve_proper. *)
Section tests.
  Context {A B : Type} `{!Equiv A, !Equiv B}.
  Context (foo : A → A) (bar : A → B) (baz : B → A → A).
  Context `{!Proper ((≡) ==> (≡)) foo,
            !Proper ((≡) ==> (≡)) bar,
            !Proper ((≡) ==> (≡) ==> (≡)) baz}.

  Definition test1 (x : A) := baz (bar (foo x)) x.
  Goal Proper ((≡) ==> (≡)) test1.
  Proof. solve_proper. Qed.

  Definition test2 (b : bool) (x : A) :=
    if b then bar (foo x) else bar x.
  Goal ∀ b, Proper ((≡) ==> (≡)) (test2 b).
  Proof. solve_proper. Qed.

  Definition test3 (f : nat → A) :=
    baz (bar (f 0)) (f 2).
  Goal Proper (pointwise_relation nat (≡) ==> (≡)) test3.
  Proof. solve_proper. Qed.

  (* We mirror [discrete_fun] from Iris to have an equivalence on a function
  space. *)
  Definition discrete_fun {A} (B : A → Type) `{!∀ x, Equiv (B x)} := ∀ x : A, B x.
  Local Instance discrete_fun_equiv  {A} {B : A → Type} `{!∀ x, Equiv (B x)} :
      Equiv (discrete_fun B) :=
    λ f g, ∀ x, f x ≡ g x.
  Notation "A -d> B" :=
    (@discrete_fun A (λ _, B) _) (at level 99, B at level 200, right associativity).
  Definition test4 x (f : A -d> A) := f x.
  Goal ∀ x, Proper ((≡) ==> (≡)) (test4 x).
  Proof. solve_proper. Qed.
End tests.

Global Instance from_option_proper_test1 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. apply _. Qed.
Global Instance from_option_proper_test2 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. solve_proper. Qed.

Section map_tests.
  Context `{FinMap K M} `{Equiv A}.

  (** For higher-order functions on maps (like [map_with_with], [fmap], etc)
  we use "higher-order [Proper] instances" [Proper ((≡) ==> (≡)) ==> ...)]
  that also allow the function to differ. We test that we can derive simpler
  [Proper]s for a fixed function using both type class inference ([apply _])
  and std++'s [solve_proper] tactic. *)
  Global Instance map_zip_proper_test1 `{Equiv B} :
    Proper ((≡@{M A}) ==> (≡@{M B}) ==> (≡@{M (A * B)})) map_zip.
  Proof. apply _. Abort.
  Global Instance map_zip_proper_test2 `{Equiv B} :
    Proper ((≡@{M A}) ==> (≡@{M B}) ==> (≡@{M (A * B)})) map_zip.
  Proof. solve_proper. Abort.
  Global Instance map_zip_with_proper_test1 `{Equiv B, Equiv C} (f : A → B → C) :
    Proper ((≡) ==> (≡) ==> (≡)) f →
    Proper ((≡) ==> (≡) ==> (≡)) (map_zip_with (M:=M) f).
  Proof. apply _. Qed.
  Global Instance map_zip_with_proper_test2 `{Equiv B, Equiv C} (f : A → B → C) :
    Proper ((≡) ==> (≡) ==> (≡)) f →
    Proper ((≡) ==> (≡) ==> (≡)) (map_zip_with (M:=M) f).
  Proof. solve_proper. Abort.
  Global Instance map_fmap_proper_test1 `{Equiv B} (f : A → B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (fmap f).
  Proof. apply _. Qed.
  Global Instance map_fmap_proper_test2 `{Equiv B} (f : A → B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (fmap f).
  Proof. solve_proper. Qed.
  Global Instance map_omap_proper_test1 `{Equiv B} (f : A → option B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (omap f).
  Proof. apply _. Qed.
  Global Instance map_omap_proper_test2 `{Equiv B} (f : A → option B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (omap f).
  Proof. solve_proper. Qed.
End map_tests.

Lemma test_prod_equivalence (X1 X2 X3 Y : propset nat * propset nat) :
  X3 ≡ X2 → X2 ≡ X1 → (X1,Y) ≡ (X3,Y).
Proof. intros H1 H2. by rewrite H1, <-H2. Qed.
