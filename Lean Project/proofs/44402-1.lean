import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h1 : a + b + (-b) = a := by rw [add_neg_cancel_right]
  have h2 : a + b + (-b) ≤ c + (-b) := by
    rw [← h1]
    apply add_le_add_left
  rw [sub_eq_add_neg] at h2
  exact h2

/- ACTUAL PROOF OF Int.le_sub_right_of_add_le -/

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h