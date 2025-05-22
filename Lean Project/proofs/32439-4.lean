import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  unfold max
  split
  · intro h
    cases h
    · exact mul_le_mul_left a (le_max_left b c)
    · exact mul_le_mul_left a (le_max_right b c)
  · intro h
    cases h
    · left
      exact mul_le_mul_left a (le_max_left b c)
    · right
      exact mul_le_mul_left a (le_max_right b c)

/- ACTUAL PROOF OF Nat.mul_max_mul_left -/

example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_max_mul_right ..