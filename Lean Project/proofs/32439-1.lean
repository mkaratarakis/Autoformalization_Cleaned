import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  rw [max_def, max_def]
  split
  · intro h
    cases h
    · calc
        a * max b c
        _ = a * b := by rw [h]
        _ = a * b := by rfl

    · calc
        a * max b c
        _ = a * c := by rw [h]
        _ = a * c := by rfl

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