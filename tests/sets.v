From stdpp Require Import sets gmap.

Lemma foo `{Set_ A C} (x : A) (X Y : C) : x ∈ X ∩ Y → x ∈ X.
Proof. intros Hx. set_unfold in Hx. tauto. Qed.

(** Test [set_unfold_list_bind]. *)
Lemma elem_of_list_bind_again {A B} (x : B) (l : list A) f :
  x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
Proof. set_solver. Qed.

(** Should not leave any evars, see issue #163 *)
Goal {[0]} ∪ dom (∅ : gmap nat nat) ≠ ∅.
Proof. set_solver. Qed.
