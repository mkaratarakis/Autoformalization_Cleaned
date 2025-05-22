import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction b with
  | zero =>
    simp only [Nat.zero_mul, min_def, min_zero_left]
  | succ b ih =>
    simp only [Nat.succ_mul, min_def]
    split
    · apply Nat.le_trans (Nat.le_min_left _ _)
      rw [Nat.mul_le_mul_right, ih]
      exact Nat.le_min (Nat.le_refl _) (Nat.le_succ _)
    · apply Nat.le_trans (Nat.le_min_right _ _)
      rw [Nat.mul_le_mul_right, ih]
      exact Nat.le_min (Nat.le_succ _) (Nat.le_refl _)

/- ACTUAL PROOF OF Nat.mul_min_mul_right -/

example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]