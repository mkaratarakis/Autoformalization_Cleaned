import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : b ≤ a) : 0 ≤ a - b := by
  have h1 : b + -b ≤ a + -b :=
    add_le_add_left (-b) h
  rw [add_neg_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.sub_nonneg_of_le -/

example {a b : Int} (h : b ≤ a) : 0 ≤ a - b := by
  have h := Int.add_le_add_right h (-b)
  rwa [Int.add_right_neg] at h