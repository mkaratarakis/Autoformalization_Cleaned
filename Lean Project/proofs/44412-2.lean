import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  calc
    a = b + (-b + a) := by rw [add_neg_cancel_left]
    _ < b + c := by apply add_lt_add_right; exact h

/- ACTUAL PROOF OF Int.lt_add_of_neg_add_lt -/

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h