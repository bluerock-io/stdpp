From stdpp Require Import strings.
From stdpp.unstable Require Import bitblast bitvector_tactics.
Unset Mangle Names.

Local Open Scope Z_scope.
Local Open Scope bv_scope.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** * Smoke tests *)

(** Simple test *)
Goal ∀ a : Z, Z_to_bv 64 a `+Z` 1 = Z_to_bv 64 (Z.succ a).
Proof.
  intros. bv_simplify. Show.
  Restart.
  intros. bv_solve.
Qed.

(** More complex test *)
Goal ∀ l r xs : bv 64, ∀ data : list (bv 64),
    bv_unsigned l < bv_unsigned r →
    bv_unsigned r ≤ Z.of_nat (length data) →
    bv_unsigned xs + Z.of_nat (length data) * 8 < 2 ^ 52 →
    bv_unsigned (xs + (bv_extract 0 64 (bv_zero_extend 128 l) +
                       bv_extract 0 64 (bv_zero_extend 128 ((r - l) ≫ BV 64 1))) * BV 64 8) < 2 ^ 52.
Proof.
  intros. bv_simplify_arith. Show.
  Restart.
  intros. bv_solve.
Qed.

(** Testing simplification in hypothesis *)
Goal ∀ l r : bv 64, ∀ data : list (bv 64),
  bv_unsigned l < bv_unsigned r →
  bv_unsigned r ≤ Z.of_nat (length data) →
  ¬ bv_signed (bv_zero_extend 128 l) >=
    bv_signed (bv_zero_extend 128 (bv_zero_extend 128 ((r - l) ≫ BV 64 1 + l + BV 64 0))) →
  bv_unsigned l < bv_unsigned ((r - l) ≫ BV 64 1 + l + BV 64 0) ≤ Z.of_nat (length data).
Proof.
  intros. bv_simplify_arith select (¬ _ >= _). bv_simplify_arith.
  split. (* We need to split since the [_ < _ ≤ _] notation differs between Coq versions. *) Show.
  Restart.
  intros. bv_simplify_arith select (¬ _ >= _). bv_solve.
Qed.

(** Testing inequality in goal. *)
Goal ∀ r1 : bv 64,
  bv_unsigned r1 ≠ 22 →
  bv_extract 0 64 (bv_zero_extend 128 r1 + BV 128 0xffffffffffffffe9 + BV 128 1) ≠ BV 64 0.
Proof.
  intros. bv_simplify. Show.
  Restart.
  intros. bv_solve.
Qed.

(** Testing inequality in hypothesis. *)
Goal ∀ i n : bv 64,
  bv_unsigned i < bv_unsigned n →
  bv_extract 0 64 (bv_zero_extend 128 n + bv_zero_extend 128 (bv_not (bv_extract 0 64 (bv_zero_extend 128 i)
          + BV 64 1)) + BV 128 1) ≠ BV 64 0 →
  bv_unsigned (bv_extract 0 64 (bv_zero_extend 128 i) + BV 64 1) < bv_unsigned n.
Proof.
  intros. bv_simplify_arith select (bv_extract _ _ _ ≠ _). bv_simplify. Show.
  Restart.
  intros. bv_simplify_arith select (bv_extract _ _ _ ≠ _). bv_solve.
Qed.

(** Testing combination of bitvector and bitblast. *)
Goal ∀ b : bv 16, ∀ v : bv 64,
  bv_or (bv_and v (BV 64 0xffffffff0000ffff)) (bv_zero_extend 64 b ≪ BV 64 16) =
  bv_concat 64 (bv_extract (16 * (1 + 1)) (16 * 2) v) (bv_concat (16 * (1 + 1)) b (bv_extract 0 (16 * 1) v)).
Proof.
  intros. bv_simplify. Show. bitblast.
Qed.
