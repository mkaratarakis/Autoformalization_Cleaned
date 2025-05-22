import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction b with
  | zero =>
    simp only [zero_mul, min_zero_left, zero_mul]
  | succ b ih =>
    simp [mul_succ, Nat.mul_succ]
    split
    · exact min_le_left (Nat.mul_le_mul_left _ _) (Nat.le_succ _)
    · rw [ih]
      exact min_le_right (Nat.le_succ _) (Nat.mul_le_mul_left _ _)

/- ACTUAL PROOF OF Nat.mul_min_mul_right -/

example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]