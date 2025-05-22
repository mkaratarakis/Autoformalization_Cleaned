import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  rw [max_eq_left, max_eq_left]
  split
  · intro h
    cases h
    · exact le_of_eq (mul_right_cancel_of_pos rfl (pos_of_ne_zero h)).symm
    · exact le_of_eq (mul_right_cancel_of_pos rfl (pos_of_ne_zero h)).symm
  · intro h
    cases h
    · left
      rw [h]
    · right
      rw [h]

/- ACTUAL PROOF OF Nat.mul_max_mul_left -/

example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_max_mul_right ..