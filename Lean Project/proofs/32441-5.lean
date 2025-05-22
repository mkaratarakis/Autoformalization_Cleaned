import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  by_cases h : b ≤ c
  · apply Nat.min_eq_left
    rw [mul_comm a b]
    rw [mul_comm a c]
    apply min_mul_right
  · apply Nat.min_eq_right
    rw [mul_comm a b]
    rw [mul_comm a c]
    apply min_mul_right

/- ACTUAL PROOF OF Nat.mul_min_mul_left -/

example (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_min_mul_right ..