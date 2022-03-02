From stdpp Require Import base tactics.
From stdpp Require Import options.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Local Set Primitive Projections.

(** Telescopes *)
Cumulative Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X → tele) : tele.

Global Arguments TeleS {_} _.

(** The telescope version of Coq's function type *)
Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => ∀ x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [tele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition tele_fold {X Y} {TT : tele} (step : ∀ {A : Type}, (A → Y) → Y) (base : X → Y)
  : (TT -t> X) → Y :=
  (fix rec {TT} : (TT -t> X) → Y :=
     match TT as TT return (TT -t> X) → Y with
     | TeleO => λ x : X, base x
     | TeleS b => λ f, step (λ x, rec (f x))
     end) TT.
Global Arguments tele_fold {_ _ !_} _ _ _ /.

(** A duplication of the type [sigT] to avoid any connection to other universes
 *)
Record tS {X : Type} (f : X -> Type) : Type :=
  { head : X;
    rest : f head }.
Global Arguments tS [X] _ : assert.

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Fixpoint tele_arg@{u} (t : tele@{u}) : Type@{u} :=
  match t with
  | TeleO => unit
  | TeleS f => tS (fun x => tele_arg (f x))
  end.
Global Arguments tele_arg _ : simpl never.
Notation TargO := tt (only parsing).
Notation TargS a b := (@Build_tS _ (fun x => tele_arg (_ x)) a b) (only parsing).

Fixpoint tele_app {TT : tele} {U} : (TT -t> U) -> tele_arg TT → U :=
  match TT as TT return (TT -t> U) -> tele_arg TT → U with
  | TeleO => λ F _, F
  | @TeleS X b => λ (F : TeleS b -t> U) '(Build_tS _ _ x b), (* b x -t> U *)
      tele_app (F x) b
  end.
(* The bidirectionality hint [&] simplifies defining tele_app-based notation
such as the atomic updates and atomic triples in Iris. *)
Global Arguments tele_app {!_ _} & _ !_ /.

Coercion tele_arg : tele >-> Sortclass.
(* This is a local coercion because otherwise, the "λ.." notation stops working. *)
Local Coercion tele_app : tele_fun >-> Funclass.

(** Inversion lemma for [tele_arg]
    Note the explicit universe annotation prevents this from being minimized
    to [Set]. The + is needed to satisfy a bug in Coq, the resulting definition
    only requires a single universe.
 *)
Lemma tele_arg_inv@{u+} {TT : tele@{u}} (a : tele_arg@{u} TT) :
  match TT as TT return tele_arg@{u} TT → Prop with
  | TeleO => λ a, a = tt
  | @TeleS t f => λ a, ∃ x a', a = {| head := x ; rest := a' |}
  end a.
Proof. destruct TT; destruct a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = ().
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X} {f : X → tele} (a : TeleS f) :
  ∃ x a', a = {| head := x ; rest := a' |}.
Proof. exact (tele_arg_inv a). Qed.

(** Map below a tele_fun *)
Fixpoint tele_map {T U} {TT : tele} : (T → U) → (TT -t> T) → TT -t> U :=
  match TT as TT return (T → U) → (TT -t> T) → TT -t> U with
  | TeleO => λ F : T → U, F
  | @TeleS X b => λ (F : T → U) (f : TeleS b -t> T) (x : X),
                  tele_map F (f x)
  end.
Global Arguments tele_map {_ _ !_} _ _ /.

Lemma tele_map_app {T U} {TT : tele} (F : T → U) (t : TT -t> T) (x : TT) :
  tele_app (tele_map F t) x = F (tele_app t x).
Proof.
  induction TT as [|X f IH]; simpl in *.
  - rewrite (tele_arg_O_inv x). done.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    unfold tele_app.
    rewrite <-IH. done.
Qed.

Global Instance tele_fmap {TT : tele} : FMap (tele_fun TT) := λ T U, tele_map.

Lemma tele_fmap_app {T U} {TT : tele} (F : T → U) (t : TT -t> T) (x : TT) :
  (F <$> t) x = F (t x).
Proof. apply tele_map_app. Qed.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {U} {TT : tele} : (tele_arg TT → U) → TT -t> U :=
  match TT as TT return (tele_arg TT → U) → TT -t> U with
  | TeleO => λ F, F tt
  | @TeleS X b => λ (F : tele_arg (TeleS b) → U) (x : X), (* b x -t> U *)
      tele_bind (λ a, F {| head := x ; rest := a |})
  end.
Global Arguments tele_bind {_ !_} _ /.

(* Show that tele_app ∘ tele_bind is the identity. *)
Lemma tele_app_bind {U} {TT : tele} (f : TT → U) x :
  (tele_app $ tele_bind f) x = f x.
Proof.
  induction TT as [|X b IH]; simpl in *.
  - rewrite (tele_arg_O_inv x). done.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
Qed.

(** We can define the identity function and composition of the [-t>] function
space. *)
Definition tele_fun_id {TT : tele} : TT -t> TT := tele_bind id.

Lemma tele_fun_id_eq {TT : tele} (x : TT) :
  tele_fun_id x = x.
Proof. unfold tele_fun_id. rewrite tele_app_bind. done. Qed.

Definition tele_fun_compose {TT1 TT2 TT3 : tele} :
  (TT2 -t> TT3) → (TT1 -t> TT2) → (TT1 -t> TT3) :=
  λ t1 t2, tele_bind (compose (tele_app t1) (tele_app t2)).

Lemma tele_fun_compose_eq {TT1 TT2 TT3 : tele} (f : TT2 -t> TT3) (g : TT1 -t> TT2) x :
  tele_fun_compose f g $ x = (f ∘ g) x.
Proof. unfold tele_fun_compose. rewrite tele_app_bind. done. Qed.

(** Notation *)
Notation "'[tele' x .. z ]" :=
  (TeleS (fun x => .. (TeleS (fun z => TeleO)) ..))
  (x binder, z binder, format "[tele  '[hv' x  ..  z ']' ]").
Notation "'[tele' ]" := (TeleO)
  (format "[tele ]").

Notation "'[tele_arg' x ; .. ; z ]" :=
  (TargS x ( .. (TargS z TargO) ..))
  (format "[tele_arg  '[hv' x ;  .. ;  z ']' ]").
Notation "'[tele_arg' ]" := (TargO)
  (format "[tele_arg ]").

(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ..' x .. y , e" :=
  (tele_app (tele_bind (λ x, .. (tele_app (tele_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e") : stdpp_scope.

(** Telescopic quantifiers *)
Definition tforall {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) (λ x, x) (tele_bind Ψ).
Global Arguments tforall {!_} _ /.
Definition texist {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold ex (λ x, x) (tele_bind Ψ).
Global Arguments texist {!_} _ /.

Notation "'∀..' x .. y , P" := (tforall (λ x, .. (tforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : stdpp_scope.
Notation "'∃..' x .. y , P" := (texist (λ x, .. (texist (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P") : stdpp_scope.

Lemma tforall_forall {TT : tele} (Ψ : TT → Prop) :
  tforall Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold tforall. induction TT as [|X ft IH].
  - simpl. split.
    + done.
    + intros ? p. rewrite (tele_arg_O_inv p). done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (tele_arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

Lemma texist_exist {TT : tele} (Ψ : TT → Prop) :
  texist Ψ ↔ ex Ψ.
Proof.
  symmetry. induction TT as [|X ft IH].
  - simpl. split.
    + intros [p Hp]. rewrite (tele_arg_O_inv p) in Hp. done.
    + intros. by exists TargO.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (tele_arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH x (λ a, Ψ (TargS x a))). eauto.
    + rewrite <-(IH p (λ a, Ψ (TargS p a))).
      intros [??]. eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Typeclasses Opaque tforall texist.
Global Hint Extern 1 (tforall _) =>
  progress cbn [tforall tele_fold tele_bind tele_app] : typeclass_instances.
Global Hint Extern 1 (texist _) =>
  progress cbn [texist tele_fold tele_bind tele_app] : typeclass_instances.
