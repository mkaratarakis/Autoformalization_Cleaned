import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < b) : a - b < 0 := by
  have h1 : a + (-b) < b + (-b) := by
    apply add_lt_add_left
    exact h
  rw [add_neg_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.sub_neg_of_lt -/

example {a b : Int} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h