From stdpp Require Export countable.
From stdpp Require Import gmap.
From stdpp Require Import options.

Record gmultiset A `{Countable A} := GMultiSet { gmultiset_car : gmap A nat }.
Global Arguments GMultiSet {_ _ _} _ : assert.
Global Arguments gmultiset_car {_ _ _} _ : assert.

Global Instance gmultiset_eq_dec `{Countable A} : EqDecision (gmultiset A).
Proof. solve_decision. Defined.

Global Program Instance gmultiset_countable `{Countable A} :
    Countable (gmultiset A) := {|
  encode X := encode (gmultiset_car X); decode p := GMultiSet <$> decode p
|}.
Next Obligation. intros A ?? [X]; simpl. by rewrite decode_encode. Qed.

Section definitions.
  Context `{Countable A}.

  Definition multiplicity (x : A) (X : gmultiset A) : nat :=
    match gmultiset_car X !! x with Some n => S n | None => 0 end.
  Global Instance gmultiset_elem_of : ElemOf A (gmultiset A) := λ x X,
    0 < multiplicity x X.
  Global Instance gmultiset_subseteq : SubsetEq (gmultiset A) := λ X Y, ∀ x,
    multiplicity x X ≤ multiplicity x Y.
  Global Instance gmultiset_equiv : Equiv (gmultiset A) := λ X Y, ∀ x,
    multiplicity x X = multiplicity x Y.

  Global Instance gmultiset_elements : Elements A (gmultiset A) := λ X,
    let (X) := X in '(x,n) ← map_to_list X; replicate (S n) x.
  Global Instance gmultiset_size : Size (gmultiset A) := length ∘ elements.

  Global Instance gmultiset_empty : Empty (gmultiset A) := GMultiSet ∅.
  Global Instance gmultiset_singleton : SingletonMS A (gmultiset A) := λ x,
    GMultiSet {[ x := 0 ]}.
  Global Instance gmultiset_union : Union (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ union_with (λ x y, Some (x `max` y)) X Y.
  Global Instance gmultiset_intersection : Intersection (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ intersection_with (λ x y, Some (x `min` y)) X Y.
  (** Often called the "sum" *)
  Global Instance gmultiset_disj_union : DisjUnion (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ union_with (λ x y, Some (S (x + y))) X Y.
  Global Instance gmultiset_difference : Difference (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ difference_with (λ x y,
      let z := x - y in guard (0 < z); Some (pred z)) X Y.

  Global Instance gmultiset_dom : Dom (gmultiset A) (gset A) := λ X,
    let (X) := X in dom X.
End definitions.

Typeclasses Opaque gmultiset_elem_of gmultiset_subseteq.
Typeclasses Opaque gmultiset_elements gmultiset_size gmultiset_empty.
Typeclasses Opaque gmultiset_singleton gmultiset_union gmultiset_difference.
Typeclasses Opaque gmultiset_dom.

Section basic_lemmas.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma gmultiset_eq X Y : X = Y ↔ ∀ x, multiplicity x X = multiplicity x Y.
  Proof.
    split; [by intros ->|intros HXY].
    destruct X as [X], Y as [Y]; f_equal; apply map_eq; intros x.
    specialize (HXY x); unfold multiplicity in *; simpl in *.
    repeat case_match; naive_solver.
  Qed.
  Global Instance gmultiset_leibniz : LeibnizEquiv (gmultiset A).
  Proof. intros X Y. by rewrite gmultiset_eq. Qed.
  Global Instance gmultiset_equiv_equivalence : Equivalence (≡@{gmultiset A}).
  Proof. constructor; repeat intro; naive_solver. Qed.

  (* Multiplicity *)
  Lemma multiplicity_empty x : multiplicity x ∅ = 0.
  Proof. done. Qed.
  Lemma multiplicity_singleton x : multiplicity x {[+ x +]} = 1.
  Proof. unfold multiplicity; simpl. by rewrite lookup_singleton. Qed.
  Lemma multiplicity_singleton_ne x y : x ≠ y → multiplicity x {[+ y +]} = 0.
  Proof. intros. unfold multiplicity; simpl. by rewrite lookup_singleton_ne. Qed.
  Lemma multiplicity_singleton' x y :
    multiplicity x {[+ y +]} = if decide (x = y) then 1 else 0.
  Proof.
    destruct (decide _) as [->|].
    - by rewrite multiplicity_singleton.
    - by rewrite multiplicity_singleton_ne.
  Qed.
  Lemma multiplicity_union X Y x :
    multiplicity x (X ∪ Y) = multiplicity x X `max` multiplicity x Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; lia.
  Qed.
  Lemma multiplicity_intersection X Y x :
    multiplicity x (X ∩ Y) = multiplicity x X `min` multiplicity x Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_intersection_with. destruct (X !! _), (Y !! _); simpl; lia.
  Qed.
  Lemma multiplicity_disj_union X Y x :
    multiplicity x (X ⊎ Y) = multiplicity x X + multiplicity x Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; lia.
  Qed.
  Lemma multiplicity_difference X Y x :
    multiplicity x (X ∖ Y) = multiplicity x X - multiplicity x Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_difference_with.
    destruct (X !! _), (Y !! _); simplify_option_eq; lia.
  Qed.

  (* Set *)
  Lemma elem_of_multiplicity x X : x ∈ X ↔ 0 < multiplicity x X.
  Proof. done. Qed.
  Lemma gmultiset_elem_of_empty x : x ∈@{gmultiset A} ∅ ↔ False.
  Proof. rewrite elem_of_multiplicity, multiplicity_empty. lia. Qed.
  Lemma gmultiset_elem_of_singleton x y : x ∈@{gmultiset A} {[+ y +]} ↔ x = y.
  Proof.
    rewrite elem_of_multiplicity, multiplicity_singleton'.
    case_decide; naive_solver lia.
  Qed.
  Lemma gmultiset_elem_of_union X Y x : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y.
  Proof. rewrite !elem_of_multiplicity, multiplicity_union. lia. Qed.
  Lemma gmultiset_elem_of_disj_union X Y x : x ∈ X ⊎ Y ↔ x ∈ X ∨ x ∈ Y.
  Proof. rewrite !elem_of_multiplicity, multiplicity_disj_union. lia. Qed.
  Lemma gmultiset_elem_of_intersection X Y x : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y.
  Proof. rewrite !elem_of_multiplicity, multiplicity_intersection. lia. Qed.

  Global Instance gmultiset_elem_of_dec : RelDecision (∈@{gmultiset A}).
  Proof. refine (λ x X, cast_if (decide (0 < multiplicity x X))); done. Defined.
End basic_lemmas.

(** * A solver for multisets *)
(** We define a tactic [multiset_solver] that solves goals involving multisets.
The strategy of this tactic is as follows:

1. Turn all equalities ([=]), equivalences ([≡]), inclusions ([⊆] and [⊂]),
   and set membership relations ([∈]) into arithmetic (in)equalities
   involving [multiplicity]. The multiplicities of [∅], [∪], [∩], [⊎] and [∖]
   are turned into [0], [max], [min], [+], and [-], respectively.
2. Decompose the goal into smaller subgoals through intuitionistic reasoning.
3. Instantiate universally quantified hypotheses in hypotheses to obtain a
   goal that can be solved using [lia].
4. Simplify multiplicities of singletons [{[ x ]}].

Step (1) and (2) are implemented using the [set_solver] tactic, which internally
calls [naive_solver] for step (2). Step (1) is implemented by extending the
[SetUnfold] mechanism with a class [MultisetUnfold].

Step (3) is implemented using the tactic [multiset_instantiate], which
instantiates universally quantified hypotheses [H : ∀ x : A, P x] in two ways:

- If the goal or some hypothesis contains [multiplicity y X] it adds the
  hypothesis [H y].
- If [P] contains a multiset singleton [{[ y ]}] it adds the hypothesis [H y].
  This is needed, for example, to prove [¬ ({[ x ]} ⊆ ∅)], which is turned
  into hypothesis [H : ∀ y, multiplicity y {[ x ]} ≤ 0] and goal [False]. The
  only way to make progress is to instantiate [H] with the singleton appearing
  in [H], so variable [x].

Step (4) is implemented using the tactic [multiset_simplify_singletons], which
simplifies occurences of [multiplicity x {[ y ]}] as follows:

- First, we try to turn these occurencess into [1] or [0] if either [x = y] or
  [x ≠ y] can be proved using [done], respectively.
- Second, we try to turn these occurences into a fresh [z ≤ 1] if [y] does not
  occur elsewhere in the hypotheses or goal.
- Finally, we make a case distinction between [x = y] or [x ≠ y]. This step is
  done last so as to avoid needless exponential blow-ups.
*)
Class MultisetUnfold `{Countable A} (x : A) (X : gmultiset A) (n : nat) :=
  { multiset_unfold : multiplicity x X = n }.
Global Arguments multiset_unfold {_ _ _} _ _ _ {_} : assert.
Global Hint Mode MultisetUnfold + + + - + - : typeclass_instances.

Section multiset_unfold.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Global Instance multiset_unfold_default x X :
    MultisetUnfold x X (multiplicity x X) | 1000.
  Proof. done. Qed.
  Global Instance multiset_unfold_empty x : MultisetUnfold x ∅ 0.
  Proof. constructor. by rewrite multiplicity_empty. Qed.
  Global Instance multiset_unfold_singleton x y :
    MultisetUnfold x {[+ x +]} 1.
  Proof. constructor. by rewrite multiplicity_singleton. Qed.
  Global Instance multiset_unfold_union x X Y n m :
    MultisetUnfold x X n → MultisetUnfold x Y m →
    MultisetUnfold x (X ∪ Y) (n `max` m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_union, HX, HY. Qed.
  Global Instance multiset_unfold_intersection x X Y n m :
    MultisetUnfold x X n → MultisetUnfold x Y m →
    MultisetUnfold x (X ∩ Y) (n `min` m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_intersection, HX, HY. Qed.
  Global Instance multiset_unfold_disj_union x X Y n m :
    MultisetUnfold x X n → MultisetUnfold x Y m →
    MultisetUnfold x (X ⊎ Y) (n + m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_disj_union, HX, HY. Qed.
  Global Instance multiset_unfold_difference x X Y n m :
    MultisetUnfold x X n → MultisetUnfold x Y m →
    MultisetUnfold x (X ∖ Y) (n - m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_difference, HX, HY. Qed.

  Global Instance set_unfold_multiset_equiv X Y f g :
    (∀ x, MultisetUnfold x X (f x)) → (∀ x, MultisetUnfold x Y (g x)) →
    SetUnfold (X ≡ Y) (∀ x, f x = g x) | 0.
  Proof.
    constructor. apply forall_proper; intros x.
    by rewrite (multiset_unfold x X (f x)), (multiset_unfold x Y (g x)).
  Qed.
  Global Instance set_unfold_multiset_eq X Y f g :
    (∀ x, MultisetUnfold x X (f x)) → (∀ x, MultisetUnfold x Y (g x)) →
    SetUnfold (X = Y) (∀ x, f x = g x) | 0.
  Proof. constructor. unfold_leibniz. by apply set_unfold_multiset_equiv. Qed.
  Global Instance set_unfold_multiset_subseteq X Y f g :
    (∀ x, MultisetUnfold x X (f x)) → (∀ x, MultisetUnfold x Y (g x)) →
    SetUnfold (X ⊆ Y) (∀ x, f x ≤ g x) | 0.
  Proof.
    constructor. apply forall_proper; intros x.
    by rewrite (multiset_unfold x X (f x)), (multiset_unfold x Y (g x)).
  Qed.
  Global Instance set_unfold_multiset_subset X Y f g :
    (∀ x, MultisetUnfold x X (f x)) → (∀ x, MultisetUnfold x Y (g x)) →
    SetUnfold (X ⊂ Y) ((∀ x, f x ≤ g x) ∧ (¬∀ x, g x ≤ f x)) | 0.
  Proof.
    constructor. unfold strict. f_equiv.
    - by apply set_unfold_multiset_subseteq.
    - f_equiv. by apply set_unfold_multiset_subseteq.
  Qed.

  Global Instance set_unfold_multiset_elem_of X x n :
    MultisetUnfold x X n → SetUnfoldElemOf x X (0 < n) | 100.
  Proof. constructor. by rewrite <-(multiset_unfold x X n). Qed.

  Global Instance set_unfold_gmultiset_empty x :
    SetUnfoldElemOf x (∅ : gmultiset A) False.
  Proof. constructor. apply gmultiset_elem_of_empty. Qed.
  Global Instance set_unfold_gmultiset_singleton x y :
    SetUnfoldElemOf x ({[+ y +]} : gmultiset A) (x = y).
  Proof. constructor; apply gmultiset_elem_of_singleton. Qed.
  Global Instance set_unfold_gmultiset_union x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ∪ Y) (P ∨ Q).
  Proof.
    intros ??; constructor. by rewrite gmultiset_elem_of_union,
      (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
  Qed.
  Global Instance set_unfold_gmultiset_disj_union x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ⊎ Y) (P ∨ Q).
  Proof.
    intros ??; constructor. rewrite gmultiset_elem_of_disj_union.
    by rewrite <-(set_unfold_elem_of x X P), <-(set_unfold_elem_of x Y Q).
  Qed.
  Global Instance set_unfold_gmultiset_intersection x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ∩ Y) (P ∧ Q).
  Proof.
    intros ??; constructor. rewrite gmultiset_elem_of_intersection.
    by rewrite (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
  Qed.
End multiset_unfold.

(** Step 3: instantiate hypotheses *)
Ltac multiset_instantiate :=
  repeat match goal with
  | H : (∀ x : ?A, @?P x) |- _ =>
     let e := mk_evar A in
     lazymatch constr:(P e) with
     | context [ {[+ ?y +]} ] => unify y e; learn_hyp (H y)
     end
  | H : (∀ x : ?A, _), _ : context [multiplicity ?y _] |- _ => learn_hyp (H y)
  | H : (∀ x : ?A, _) |- context [multiplicity ?y _] => learn_hyp (H y)
  end.

(** Step 4: simplify singletons *)
Local Lemma multiplicity_singleton_forget `{Countable A} x y :
  ∃ n, multiplicity (A:=A) x {[+ y +]} = n ∧ n ≤ 1.
Proof. rewrite multiplicity_singleton'. case_decide; eauto with lia. Qed.

Ltac multiset_simplify_singletons :=
  repeat match goal with
  | H : context [multiplicity ?x {[+ ?y +]}] |- _ =>
     first
       [progress rewrite ?multiplicity_singleton, ?multiplicity_singleton_ne in H by done
       |destruct (multiplicity_singleton_forget x y) as (?&->&?); clear y
       |rewrite multiplicity_singleton' in H; destruct (decide (x = y)); simplify_eq/=]
  | |- context [multiplicity ?x {[+ ?y +]}] =>
     first
       [progress rewrite ?multiplicity_singleton, ?multiplicity_singleton_ne by done
       |destruct (multiplicity_singleton_forget x y) as (?&->&?); clear y
       |rewrite multiplicity_singleton'; destruct (decide (x = y)); simplify_eq/=]
  end.

(** Putting it all together *)
Ltac multiset_solver :=
  set_solver by (multiset_instantiate; multiset_simplify_singletons; lia).

Section more_lemmas.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  (* Algebraic laws *)
  (** For union *)
  Global Instance gmultiset_union_comm : Comm (=@{gmultiset A}) (∪).
  Proof. unfold Comm. multiset_solver. Qed.
  Global Instance gmultiset_union_assoc : Assoc (=@{gmultiset A}) (∪).
  Proof. unfold Assoc. multiset_solver. Qed.
  Global Instance gmultiset_union_left_id : LeftId (=@{gmultiset A}) ∅ (∪).
  Proof. unfold LeftId. multiset_solver. Qed.
  Global Instance gmultiset_union_right_id : RightId (=@{gmultiset A}) ∅ (∪).
  Proof. unfold RightId. multiset_solver. Qed.
  Global Instance gmultiset_union_idemp : IdemP (=@{gmultiset A}) (∪).
  Proof. unfold IdemP. multiset_solver. Qed.

  (** For intersection *)
  Global Instance gmultiset_intersection_comm : Comm (=@{gmultiset A}) (∩).
  Proof. unfold Comm. multiset_solver. Qed.
  Global Instance gmultiset_intersection_assoc : Assoc (=@{gmultiset A}) (∩).
  Proof. unfold Assoc. multiset_solver. Qed.
  Global Instance gmultiset_intersection_left_absorb : LeftAbsorb (=@{gmultiset A}) ∅ (∩).
  Proof. unfold LeftAbsorb. multiset_solver. Qed.
  Global Instance gmultiset_intersection_right_absorb : RightAbsorb (=@{gmultiset A}) ∅ (∩).
  Proof. unfold RightAbsorb. multiset_solver. Qed.
  Global Instance gmultiset_intersection_idemp : IdemP (=@{gmultiset A}) (∩).
  Proof. unfold IdemP. multiset_solver. Qed.

  Lemma gmultiset_union_intersection_l X Y Z : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_intersection_r X Y Z : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z).
  Proof. multiset_solver. Qed.
  Lemma gmultiset_intersection_union_l X Y Z : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).
  Proof. multiset_solver. Qed.
  Lemma gmultiset_intersection_union_r X Y Z : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z).
  Proof. multiset_solver. Qed.

  (** For disjoint union (aka sum) *)
  Global Instance gmultiset_disj_union_comm : Comm (=@{gmultiset A}) (⊎).
  Proof. unfold Comm. multiset_solver. Qed.
  Global Instance gmultiset_disj_union_assoc : Assoc (=@{gmultiset A}) (⊎).
  Proof. unfold Assoc. multiset_solver. Qed.
  Global Instance gmultiset_disj_union_left_id : LeftId (=@{gmultiset A}) ∅ (⊎).
  Proof. unfold LeftId. multiset_solver. Qed.
  Global Instance gmultiset_disj_union_right_id : RightId (=@{gmultiset A}) ∅ (⊎).
  Proof. unfold RightId. multiset_solver. Qed.

  Global Instance gmultiset_disj_union_inj_1 X : Inj (=) (=) (X ⊎.).
  Proof. unfold Inj. multiset_solver. Qed.
  Global Instance gmultiset_disj_union_inj_2 X : Inj (=) (=) (.⊎ X).
  Proof. unfold Inj. multiset_solver. Qed.

  Lemma gmultiset_disj_union_intersection_l X Y Z : X ⊎ (Y ∩ Z) = (X ⊎ Y) ∩ (X ⊎ Z).
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_intersection_r X Y Z : (X ∩ Y) ⊎ Z = (X ⊎ Z) ∩ (Y ⊎ Z).
  Proof. multiset_solver. Qed.

  Lemma gmultiset_disj_union_union_l X Y Z : X ⊎ (Y ∪ Z) = (X ⊎ Y) ∪ (X ⊎ Z).
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_union_r X Y Z : (X ∪ Y) ⊎ Z = (X ⊎ Z) ∪ (Y ⊎ Z).
  Proof. multiset_solver. Qed.

  (** Element of operation *)
  Lemma gmultiset_not_elem_of_empty x : x ∉@{gmultiset A} ∅.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_not_elem_of_singleton x y : x ∉@{gmultiset A} {[+ y +]} ↔ x ≠ y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
  Proof. multiset_solver. Qed.

  (** Misc *)
  Global Instance gmultiset_singleton_inj : Inj (=) (=@{gmultiset A}) singletonMS.
  Proof.
    intros x1 x2 Hx. rewrite gmultiset_eq in Hx. specialize (Hx x1).
    rewrite multiplicity_singleton, multiplicity_singleton' in Hx.
    case_decide; [done|lia].
  Qed.
  Lemma gmultiset_non_empty_singleton x : {[+ x +]} ≠@{gmultiset A} ∅.
  Proof. multiset_solver. Qed.

  (** Conversion from lists *)
  Lemma list_to_set_disj_nil : list_to_set_disj [] =@{gmultiset A} ∅.
  Proof. done. Qed.
  Lemma list_to_set_disj_cons x l :
    list_to_set_disj (x :: l) =@{gmultiset A} {[+ x +]} ⊎ list_to_set_disj l.
  Proof. done. Qed.
  Lemma list_to_set_disj_app l1 l2 :
    list_to_set_disj (l1 ++ l2) =@{gmultiset A} list_to_set_disj l1 ⊎ list_to_set_disj l2.
  Proof. induction l1; multiset_solver. Qed.
  Lemma elem_of_list_to_set_disj x l :
    x ∈@{gmultiset A} list_to_set_disj l ↔ x ∈ l.
  Proof. induction l; set_solver. Qed.
  Global Instance list_to_set_disj_perm :
    Proper ((≡ₚ) ==> (=)) (list_to_set_disj (C:=gmultiset A)).
  Proof. induction 1; multiset_solver. Qed.

  (** Properties of the elements operation *)
  Lemma gmultiset_elements_empty : elements (∅ : gmultiset A) = [].
  Proof.
    unfold elements, gmultiset_elements; simpl. by rewrite map_to_list_empty.
  Qed.
  Lemma gmultiset_elements_empty_iff X : elements X = [] ↔ X = ∅.
  Proof.
    split; [|intros ->; by rewrite gmultiset_elements_empty].
    destruct X as [X]; unfold elements, gmultiset_elements; simpl.
    intros; apply (f_equal GMultiSet). destruct (map_to_list X) as [|[]] eqn:?.
    - by apply map_to_list_empty_iff.
    - naive_solver.
  Qed.
  Lemma gmultiset_elements_empty_inv X : elements X = [] → X = ∅.
  Proof. apply gmultiset_elements_empty_iff. Qed.

  Lemma gmultiset_elements_singleton x : elements ({[+ x +]} : gmultiset A) = [ x ].
  Proof.
    unfold elements, gmultiset_elements; simpl. by rewrite map_to_list_singleton.
  Qed.
  Lemma gmultiset_elements_disj_union X Y :
    elements (X ⊎ Y) ≡ₚ elements X ++ elements Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold elements, gmultiset_elements.
    set (f xn := let '(x, n) := xn in replicate (S n) x); simpl.
    revert Y; induction X as [|x n X HX IH] using map_ind; intros Y.
    { by rewrite (left_id_L _ _ Y), map_to_list_empty. }
    destruct (Y !! x) as [n'|] eqn:HY.
    - rewrite <-(insert_delete Y x n') by done.
      erewrite <-insert_union_with by done.
      rewrite !map_to_list_insert, !bind_cons
        by (by rewrite ?lookup_union_with, ?lookup_delete, ?HX).
      rewrite (assoc_L _), <-(comm (++) (f (_,n'))), <-!(assoc_L _), <-IH.
      rewrite (assoc_L _). f_equiv.
      rewrite (comm _); simpl. by rewrite replicate_plus, Permutation_middle.
    - rewrite <-insert_union_with_l, !map_to_list_insert, !bind_cons
        by (by rewrite ?lookup_union_with, ?HX, ?HY).
      by rewrite <-(assoc_L (++)), <-IH.
  Qed.
  Lemma gmultiset_elem_of_elements x X : x ∈ elements X ↔ x ∈ X.
  Proof.
    destruct X as [X]. unfold elements, gmultiset_elements.
    set (f xn := let '(x, n) := xn in replicate (S n) x); simpl.
    unfold elem_of at 2, gmultiset_elem_of, multiplicity; simpl.
    rewrite elem_of_list_bind. split.
    - intros [[??] [[<- ?]%elem_of_replicate ->%elem_of_map_to_list]]; lia.
    - intros. destruct (X !! x) as [n|] eqn:Hx; [|lia].
      exists (x,n); split; [|by apply elem_of_map_to_list].
      apply elem_of_replicate; auto with lia.
  Qed.
  Lemma gmultiset_elem_of_dom x X : x ∈ dom X ↔ x ∈ X.
  Proof.
    unfold dom, gmultiset_dom, elem_of at 2, gmultiset_elem_of, multiplicity.
    destruct X as [X]; simpl; rewrite elem_of_dom, <-not_eq_None_Some.
    destruct (X !! x); naive_solver lia.
  Qed.

  (** Properties of the set_fold operation *)
  Lemma gmultiset_set_fold_empty {B} (f : A → B → B) (b : B) :
    set_fold f b (∅ : gmultiset A) = b.
  Proof. by unfold set_fold; simpl; rewrite gmultiset_elements_empty. Qed.
  Lemma gmultiset_set_fold_singleton {B} (f : A → B → B) (b : B) (a : A) :
    set_fold f b ({[+ a +]} : gmultiset A) = f a b.
  Proof. by unfold set_fold; simpl; rewrite gmultiset_elements_singleton. Qed.
  Lemma gmultiset_set_fold_disj_union (f : A → A → A) (b : A) X Y :
    Comm (=) f →
    Assoc (=) f →
    set_fold f b (X ⊎ Y) = set_fold f (set_fold f b X) Y.
  Proof.
    intros Hcomm Hassoc. unfold set_fold; simpl.
    by rewrite gmultiset_elements_disj_union, <- foldr_app, (comm (++)).
  Qed.

  (** Properties of the size operation *)
  Lemma gmultiset_size_empty : size (∅ : gmultiset A) = 0.
  Proof. done. Qed.
  Lemma gmultiset_size_empty_iff X : size X = 0 ↔ X = ∅.
  Proof.
    unfold size, gmultiset_size; simpl.
    by rewrite length_zero_iff_nil, gmultiset_elements_empty_iff.
  Qed.
  Lemma gmultiset_size_empty_inv X : size X = 0 → X = ∅.
  Proof. apply gmultiset_size_empty_iff. Qed.
  Lemma gmultiset_size_non_empty_iff X : size X ≠ 0 ↔ X ≠ ∅.
  Proof. by rewrite gmultiset_size_empty_iff. Qed.

  Lemma gmultiset_choose_or_empty X : (∃ x, x ∈ X) ∨ X = ∅.
  Proof.
    destruct (elements X) as [|x l] eqn:HX; [right|left].
    - by apply gmultiset_elements_empty_iff.
    - exists x. rewrite <-gmultiset_elem_of_elements, HX. by left.
  Qed.
  Lemma gmultiset_choose X : X ≠ ∅ → ∃ x, x ∈ X.
  Proof. intros. by destruct (gmultiset_choose_or_empty X). Qed.
  Lemma gmultiset_size_pos_elem_of X : 0 < size X → ∃ x, x ∈ X.
  Proof.
    intros Hsz. destruct (gmultiset_choose_or_empty X) as [|HX]; [done|].
    contradict Hsz. rewrite HX, gmultiset_size_empty; lia.
  Qed.

  Lemma gmultiset_size_singleton x : size ({[+ x +]} : gmultiset A) = 1.
  Proof.
    unfold size, gmultiset_size; simpl. by rewrite gmultiset_elements_singleton.
  Qed.
  Lemma gmultiset_size_disj_union X Y : size (X ⊎ Y) = size X + size Y.
  Proof.
    unfold size, gmultiset_size; simpl.
    by rewrite gmultiset_elements_disj_union, app_length.
  Qed.

  (** Order stuff *)
  Global Instance gmultiset_po : PartialOrder (⊆@{gmultiset A}).
  Proof. repeat split; repeat intro; multiset_solver. Qed.

  Lemma gmultiset_subseteq_alt X Y :
    X ⊆ Y ↔
    map_relation (≤) (λ _, False) (λ _, True) (gmultiset_car X) (gmultiset_car Y).
  Proof.
    apply forall_proper; intros x. unfold multiplicity.
    destruct (gmultiset_car X !! x), (gmultiset_car Y !! x); naive_solver lia.
  Qed.
  Global Instance gmultiset_subseteq_dec : RelDecision (⊆@{gmultiset A}).
  Proof.
   refine (λ X Y, cast_if (decide (map_relation (≤)
     (λ _, False) (λ _, True) (gmultiset_car X) (gmultiset_car Y))));
     by rewrite gmultiset_subseteq_alt.
  Defined.

  Lemma gmultiset_subset_subseteq X Y : X ⊂ Y → X ⊆ Y.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_empty_subseteq X : ∅ ⊆ X.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_union_subseteq_l X Y : X ⊆ X ∪ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_subseteq_r X Y : Y ⊆ X ∪ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_mono X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_disj_union_subseteq_l X Y : X ⊆ X ⊎ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_subseteq_r X Y : Y ⊆ X ⊎ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_mono X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ⊎ Y1 ⊆ X2 ⊎ Y2.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ⊎ Y1 ⊆ X ⊎ Y2.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ⊎ Y ⊆ X2 ⊎ Y.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_subset X Y : X ⊆ Y → size X < size Y → X ⊂ Y.
  Proof. intros. apply strict_spec_alt; split; naive_solver auto with lia. Qed.
  Lemma gmultiset_disj_union_subset_l X Y : Y ≠ ∅ → X ⊂ X ⊎ Y.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_union_subset_r X Y : X ≠ ∅ → Y ⊂ X ⊎ Y.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_singleton_subseteq_l x X : {[+ x +]} ⊆ X ↔ x ∈ X.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_singleton_subseteq x y :
    {[+ x +]} ⊆@{gmultiset A} {[+ y +]} ↔ x = y.
  Proof.
    split; [|multiset_solver].
    (* FIXME: [multiset_solver] should solve this *)
    intros Hxy. specialize (Hxy x).
    rewrite multiplicity_singleton, multiplicity_singleton' in Hxy.
    case_decide; [done|lia].
  Qed.

  Lemma gmultiset_elem_of_subseteq X1 X2 x : x ∈ X1 → X1 ⊆ X2 → x ∈ X2.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_disj_union_difference X Y : X ⊆ Y → Y = X ⊎ Y ∖ X.
  Proof. multiset_solver. Qed.
  Lemma gmultiset_disj_union_difference' x Y :
    x ∈ Y → Y = {[+ x +]} ⊎ Y ∖ {[+ x +]}.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_size_difference X Y : Y ⊆ X → size (X ∖ Y) = size X - size Y.
  Proof.
    intros HX%gmultiset_disj_union_difference.
    rewrite HX at 2; rewrite gmultiset_size_disj_union. lia.
  Qed.

  Lemma gmultiset_empty_difference X Y : Y ⊆ X → Y ∖ X = ∅.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_non_empty_difference X Y : X ⊂ Y → Y ∖ X ≠ ∅.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_difference_diag X : X ∖ X = ∅.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_difference_subset X Y : X ≠ ∅ → X ⊆ Y → Y ∖ X ⊂ Y.
  Proof. multiset_solver. Qed.

  Lemma gmultiset_difference_disj_union_r X Y Z : X ∖ Y = (X ⊎ Z) ∖ (Y ⊎ Z).
  Proof. multiset_solver. Qed.

  Lemma gmultiset_difference_disj_union_l X Y Z : X ∖ Y = (Z ⊎ X) ∖ (Z ⊎ Y).
  Proof. multiset_solver. Qed.

  (** Mononicity *)
  Lemma gmultiset_elements_submseteq X Y : X ⊆ Y → elements X ⊆+ elements Y.
  Proof.
    intros ->%gmultiset_disj_union_difference. rewrite gmultiset_elements_disj_union.
    by apply submseteq_inserts_r.
  Qed.

  Lemma gmultiset_subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
  Proof. intros. by apply submseteq_length, gmultiset_elements_submseteq. Qed.

  Lemma gmultiset_subset_size X Y : X ⊂ Y → size X < size Y.
  Proof.
    intros HXY. assert (size (Y ∖ X) ≠ 0).
    { by apply gmultiset_size_non_empty_iff, gmultiset_non_empty_difference. }
    rewrite (gmultiset_disj_union_difference X Y),
      gmultiset_size_disj_union by auto using gmultiset_subset_subseteq. lia.
  Qed.

  (** Well-foundedness *)
  Lemma gmultiset_wf : wf (⊂@{gmultiset A}).
  Proof.
    apply (wf_projected (<) size); auto using gmultiset_subset_size, lt_wf.
  Qed.

  Lemma gmultiset_ind (P : gmultiset A → Prop) :
    P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
  Proof.
    intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
    destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
    rewrite (gmultiset_disj_union_difference' x X) by done.
    apply Hinsert, IH; multiset_solver.
  Qed.
End more_lemmas.
