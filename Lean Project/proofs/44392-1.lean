import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a - b < 0) : a < b := by
  have h1 : a - b + b < 0 + b := by
    exact add_lt_add_right h b
  rw [sub_add_cancel, zero_add] at h1
  exact h1

/- ACTUAL PROOF OF Int.lt_of_sub_neg -/

example {a b : Int} (h : a - b < 0) : a < b := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h