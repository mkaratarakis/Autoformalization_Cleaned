import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a < b + c) : a - b < c := by
  have h1 : a + -b < (b + c) + -b := by
    exact add_lt_add_left h _
  have h2 : (b + c) + -b = c := by
    rw [add_assoc, add_left_neg]
  rwa [h2] at h1

/- ACTUAL PROOF OF Int.sub_left_lt_of_lt_add -/

example {a b c : Int} (h : a < b + c) : a - b < c := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h