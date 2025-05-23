import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by
  have h1 : a + -b ≤ b + -b := by
    apply add_le_add_left
    exact h
  rw [add_neg_cancel_right] at h1
  exact h1

/- ACTUAL PROOF OF Int.sub_nonpos_of_le -/

example {a b : Int} (h : a ≤ b) : a - b ≤ 0 := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h