import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction b with
  | zero =>
    simp only [Nat.zero_mul, min_eq_left, MulZeroClass.zero_mul]
  | succ b ih =>
    rw [Nat.succ_mul, Nat.mul_succ, min_eq_left, min_eq_right]
    split
    · rw [ih]
      apply min_le_left
      apply Nat.mul_le_mul_left
    · rw [ih]
      apply min_le_right
      apply Nat.mul_le_mul_left

/- ACTUAL PROOF OF Nat.mul_min_mul_right -/

example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]