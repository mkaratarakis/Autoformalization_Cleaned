import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h1 : a + -b ≤ (b + c) + -b := by
    exact add_le_add_left h (-b)
  rw [add_assoc, add_right_neg] at h1
  rw [sub_eq_add_neg]
  exact h1

/- ACTUAL PROOF OF Int.sub_left_le_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h