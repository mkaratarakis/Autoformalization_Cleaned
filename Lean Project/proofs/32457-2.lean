import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction b with
  | zero =>
    simp [zero_mul]
  | succ b ih =>
    simp [Nat.succ_mul]
    split <;> rw [ih]
    · apply min_le_left
      exact Nat.mul_le_mul_left a c
    · apply min_le_right
      simp [Nat.mul_comm, Nat.mul_succ]
      apply Nat.le_add_right

/- ACTUAL PROOF OF Nat.mul_min_mul_right -/

example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]