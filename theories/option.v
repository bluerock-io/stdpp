(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on the option
data type that are not in the Coq standard library. *)
Require Export base tactics decidable.

(** * General definitions and theorems *)
(** Basic properties about equality. *)
Lemma None_ne_Some `(a : A) : None ≠ Some a.
Proof. congruence. Qed.
Lemma Some_ne_None `(a : A) : Some a ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some `(x : option A) a : x = None → x ≠ Some a.
Proof. congruence. Qed.
Instance Some_inj {A} : Injective (=) (=) (@Some A).
Proof. congruence. Qed.

(** The non dependent elimination principle on the option type. *)
Definition option_case {A B} (f : A → B) (b : B) (x : option A) : B :=
  match x with
  | None => b
  | Some a => f a
  end.

(** The [from_option] function allows us to get the value out of the option
type by specifying a default value. *)
Definition from_option {A} (a : A) (x : option A) : A :=
  match x with
  | None => a
  | Some b => b
  end.

(** An alternative, but equivalent, definition of equality on the option
data type. This theorem is useful to prove that two options are the same. *)
Lemma option_eq {A} (x y : option A) :
  x = y ↔ ∀ a, x = Some a ↔ y = Some a.
Proof.
  split.
  { intros. by subst. }
  intros E. destruct x, y.
  + by apply E.
  + symmetry. by apply E.
  + by apply E.
  + done.
Qed.

Inductive is_Some {A} : option A → Prop :=
  make_is_Some x : is_Some (Some x).

Lemma make_is_Some_alt `(x : option A) a : x = Some a → is_Some x.
Proof. intros. by subst. Qed.
Hint Resolve make_is_Some_alt.
Lemma is_Some_None {A} : ¬is_Some (@None A).
Proof. by inversion 1. Qed.
Hint Resolve is_Some_None.

Lemma is_Some_alt `(x : option A) : is_Some x ↔ ∃ y, x = Some y.
Proof. split. inversion 1; eauto. intros [??]. by subst. Qed.

Ltac inv_is_Some := repeat
  match goal with
  | H : is_Some _ |- _ => inversion H; clear H; subst
  end.

Definition is_Some_proj `{x : option A} : is_Some x → A :=
  match x with
  | Some a => λ _, a
  | None => False_rect _ ∘ is_Some_None
  end.
Definition Some_dec `(x : option A) : { a | x = Some a } + { x = None } :=
  match x return { a | x = Some a } + { x = None } with
  | Some a => inleft (a ↾ eq_refl _)
  | None => inright eq_refl
  end.
Instance is_Some_dec `(x : option A) : Decision (is_Some x) :=
  match x with
  | Some x => left (make_is_Some x)
  | None => right is_Some_None
  end.
Instance None_dec `(x : option A) : Decision (x = None) :=
  match x with
  | Some x => right (Some_ne_None x)
  | None => left eq_refl
  end.

Lemma eq_None_not_Some `(x : option A) : x = None ↔ ¬is_Some x.
Proof. split. by destruct 2. destruct x. by intros []. done. Qed.
Lemma not_eq_None_Some `(x : option A) : x ≠ None ↔ is_Some x.
Proof. rewrite eq_None_not_Some. split. apply dec_stable. tauto. Qed.

Lemma make_eq_Some {A} (x : option A) a :
  is_Some x → (∀ b, x = Some b → b = a) → x = Some a.
Proof. destruct 1. intros. f_equal. auto. Qed.

(** Equality on [option] is decidable. *)
Instance option_eq_dec `{dec : ∀ x y : A, Decision (x = y)}
    (x y : option A) : Decision (x = y) :=
  match x, y with
  | Some a, Some b =>
     match dec a b with
     | left H => left (f_equal _ H)
     | right H => right (H ∘ injective Some _ _)
     end
  | Some _, None => right (Some_ne_None _)
  | None, Some _ => right (None_ne_Some _)
  | None, None => left eq_refl
  end.

(** * Monadic operations *)
Instance option_ret: MRet option := @Some.
Instance option_bind: MBind option := λ A B f x,
  match x with
  | Some a => f a
  | None => None
  end.
Instance option_join: MJoin option := λ A x,
  match x with
  | Some x => x
  | None => None
  end.
Instance option_fmap: FMap option := @option_map.
Instance option_guard: MGuard option := λ P dec A x,
  if dec then x else None.

Lemma fmap_is_Some {A B} (f : A → B) (x : option A) :
  is_Some (f <$> x) ↔ is_Some x.
Proof. split; inversion 1. by destruct x. done. Qed.
Lemma fmap_Some {A B} (f : A → B) (x : option A) y :
  f <$> x = Some y ↔ ∃ x', x = Some x' ∧ y = f x'.
Proof. unfold fmap, option_fmap. destruct x; naive_solver. Qed.
Lemma fmap_None {A B} (f : A → B) (x : option A) :
  f <$> x = None ↔ x = None.
Proof. unfold fmap, option_fmap. by destruct x. Qed.

Lemma option_fmap_id {A} (x : option A) :
  id <$> x = x.
Proof. by destruct x. Qed.
Lemma option_bind_assoc {A B C} (f : A → option B)
    (g : B → option C) (x : option A) : (x ≫= f) ≫= g = x ≫= (mbind g ∘ f).
Proof. by destruct x; simpl. Qed.

Tactic Notation "simplify_option_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => first [progress simpl in * | progress simplify_equality]
  | H : context [mbind (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in
    first
      [ let x := fresh in evar (x:A);
        let x' := eval unfold x in x in clear x;
        assert (o = Some x') as Hx by tac
      | assert (o = None) as Hx by tac ];
    rewrite Hx in H; clear Hx
  | H : context [fmap (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in
    first
      [ let x := fresh in evar (x:A);
        let x' := eval unfold x in x in clear x;
        assert (o = Some x') as Hx by tac
      | assert (o = None) as Hx by tac ];
    rewrite Hx in H; clear Hx
  | H : context [ match ?o with _ => _ end ] |- _ =>
    match type of o with
    | option ?A =>
      let Hx := fresh in
      first
        [ let x := fresh in evar (x:A);
          let x' := eval unfold x in x in clear x;
          assert (o = Some x') as Hx by tac
        | assert (o = None) as Hx by tac ];
      rewrite Hx in H; clear Hx
    end
  | H : mbind (M:=option) ?f ?o = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : ?x = mbind (M:=option) ?f ?o |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : fmap (M:=option) ?f ?o = ?x |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | H : ?x = fmap (M:=option) ?f ?o |- _ =>
    match o with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match x with Some _ => idtac | None => idtac | _ => fail 1 end;
    destruct o eqn:?
  | |- context [mbind (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in
    first
      [ let x := fresh in evar (x:A);
        let x' := eval unfold x in x in clear x;
        assert (o = Some x') as Hx by tac
      | assert (o = None) as Hx by tac ];
    rewrite Hx; clear Hx
  | |- context [fmap (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in
    first
      [ let x := fresh in evar (x:A);
        let x' := eval unfold x in x in clear x;
        assert (o = Some x') as Hx by tac
      | assert (o = None) as Hx by tac ];
    rewrite Hx; clear Hx
  | |- context [ match ?o with _ => _ end ] =>
    match type of o with
    | option ?A =>
      let Hx := fresh in
      first
        [ let x := fresh in evar (x:A);
          let x' := eval unfold x in x in clear x;
          assert (o = Some x') as Hx by tac
        | assert (o = None) as Hx by tac ];
      rewrite Hx; clear Hx
    end
  | H : context C [@mguard option _ ?P ?dec _ ?x] |- _ =>
    let X := context C [ if dec then x else None ] in
    change X in H; destruct_decide dec
  | |- context C [@mguard option _ ?P ?dec _ ?x] =>
    let X := context C [ if dec then x else None ] in
    change X; destruct_decide dec
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | H1 : ?o = Some ?x, H2 : ?o = None |- _ =>
    congruence
  end.
Tactic Notation "simplify_option_equality" :=
  simplify_option_equality by eauto.

Hint Extern 100 => simplify_option_equality : simplify_option_equality.

(** * Union, intersection and difference *)
Instance option_union_with {A} : UnionWith A (option A) := λ f x y,
  match x, y with
  | Some a, Some b => f a b
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.
Instance option_intersection_with {A} :
    IntersectionWith A (option A) := λ f x y,
  match x, y with
  | Some a, Some b => f a b
  | _, _ => None
  end.
Instance option_difference_with {A} :
    DifferenceWith A (option A) := λ f x y,
  match x, y with
  | Some a, Some b => f a b
  | Some a, None => Some a
  | None, _ => None
  end.

Section option_union_intersection_difference.
  Context {A} (f : A → A → option A).

  Global Instance: LeftId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: RightId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (union_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(commutative f). Qed.

  Global Instance: LeftAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: RightAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance: Commutative (=) f → Commutative (=) (intersection_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(commutative f). Qed.

  Global Instance: RightId (=) None (difference_with f).
  Proof. by intros [?|]. Qed.
End option_union_intersection_difference.
