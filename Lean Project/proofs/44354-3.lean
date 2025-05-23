import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : 0 ≤ b) : a ≤ b + a := by
  have h1 : 0 + a ≤ b + a := by
    exact Nat.add_le_add_left h a
  rw [Nat.zero_add] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_add_of_nonneg_left -/

example {a b : Int} (h : 0 ≤ b) : a ≤ b + a := by
  have : 0 + a ≤ b + a := Int.add_le_add_right h a
  rwa [Int.zero_add] at this