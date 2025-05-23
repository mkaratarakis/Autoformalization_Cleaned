import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  rw [← add_neg_assoc]
  exact add_le_add_left h (-b)

/- ACTUAL PROOF OF Int.sub_left_le_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : a - b ≤ c := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_comm b c, Int.add_neg_cancel_right] at h