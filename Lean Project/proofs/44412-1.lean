import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h1 := add_lt_add_left h b
  rw [add_assoc, add_neg_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.lt_add_of_neg_add_lt -/

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  have h := Int.add_lt_add_left h b
  rwa [Int.add_neg_cancel_left] at h