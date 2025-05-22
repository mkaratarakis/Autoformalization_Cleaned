import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  by_cases h : b ≤ c
  · calc
      min (a + b) (a + c)
        = a + b := by rw [min_eq_left]; exact Nat.add_le_add_right h _
      _ = a + min b c := by rw [min_eq_left]; exact h
  · calc
      min (a + b) (a + c)
        = a + c := by rw [min_eq_right]; exact Nat.add_le_add_right (not_le.1 h) _
      _ = a + min b c := by rw [min_eq_right]; exact not_le.1 h

/- ACTUAL PROOF OF Nat.add_min_add_left -/

example (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_min_add_right ..