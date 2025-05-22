import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  have h₁ : a ^ n * 1 = a ^ n := rfl
  have h₂ : a ^ (n + 1) = a ^ n * a := rfl
  rw [h₁, h₂]
  apply mul_lt_mul_left
  · exact h
  · norm_num

/- ACTUAL PROOF OF Nat.pow_lt_pow_succ -/

example (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  rw [← Nat.mul_one (a^n), Nat.pow_succ]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) h (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h))