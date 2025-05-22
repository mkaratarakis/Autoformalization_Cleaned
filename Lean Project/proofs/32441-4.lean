import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  cases h : leRfl b with
  | inl h =>
    rw [min_eq_left h]
    rw [min_eq_left (mul_le_mul_left a c)]
  | inr h =>
    rw [min_eq_right h]
    rw [min_eq_right (mul_le_mul_left a b)]

/- ACTUAL PROOF OF Nat.mul_min_mul_left -/

example (a b c : Nat) : min (a * b) (a * c) = a * min b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_min_mul_right ..