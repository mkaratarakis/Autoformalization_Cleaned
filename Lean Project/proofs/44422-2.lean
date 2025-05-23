import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a < b + c) : a - c < b := by
  have h1 : a + (-c) < b + c + (-c) := by
    apply add_lt_add_left
    exact h
  have h2 : b + c + (-c) = b := by
    rw [add_assoc, add_left_neg]
  have h3 : a + (-c) = a - c := by
    rfl
  rw [h2, h3] at h1
  exact h1

/- ACTUAL PROOF OF Int.sub_right_lt_of_lt_add -/

example {a b c : Int} (h : a < b + c) : a - c < b := by
  have h := Int.add_lt_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h