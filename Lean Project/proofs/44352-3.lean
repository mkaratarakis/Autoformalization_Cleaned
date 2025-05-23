import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : 0 < a - b) : b < a := by
  have h1 : 0 + b < a - b + b := by
    simp [add_zero, add_sub_cancel]
    exact h
  rwa [zero_add] at h1

/- ACTUAL PROOF OF Int.lt_of_sub_pos -/

example {a b : Int} (h : 0 < a - b) : b < a := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h