import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  rw [add_assoc, add_neg_cancel_right] at h
  rw [sub_eq_add_neg]
  exact h

/- ACTUAL PROOF OF Int.le_sub_right_of_add_le -/

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h