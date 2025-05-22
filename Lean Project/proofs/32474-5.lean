import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  rw [pow_succ']
  exact Nat.mul_lt_mul_of_pos_left (a ^ n) h (pow_pos (show 0 < a from Nat.zero_lt_one.trans h) _)

/- ACTUAL PROOF OF Nat.pow_lt_pow_succ -/

example (h : 1 < a) : a ^ n < a ^ (n + 1) := by
  rw [← Nat.mul_one (a^n), Nat.pow_succ]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) h (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h))