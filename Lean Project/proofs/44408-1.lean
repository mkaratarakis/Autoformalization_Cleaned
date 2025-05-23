import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : a - c ≤ b := by
  have h1 := add_le_add_left h (-c)
  rwa [add_neg_cancel_right, add_comm] at h1

/- ACTUAL PROOF OF Int.sub_right_le_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : a - c ≤ b := by
  have h := Int.add_le_add_right h (-c)
  rwa [Int.add_neg_cancel_right] at h