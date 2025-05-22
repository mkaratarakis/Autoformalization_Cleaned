import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  by_cases h : b ≤ c
  · simp [h, max_eq_right h]
    exact add_le_add_right (le_max_left _ _) _
  · simp [h, max_eq_left (not_le.mp h)]
    exact add_le_add_right (le_max_right _ _) _

/- ACTUAL PROOF OF Nat.add_max_add_left -/

example (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_max_add_right ..