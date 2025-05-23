import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h1 : a ≤ c + -b := by
    apply add_le_add_left
    exact h
  rw [add_comm (-b) c, ← neg_add] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_sub_right_of_add_le -/

example {a b c : Int} (h : a + b ≤ c) : a ≤ c - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_neg_cancel_right] at h