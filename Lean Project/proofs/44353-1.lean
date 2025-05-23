import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : 0 ≤ a - b) : b ≤ a := by
  have h1 : 0 + b ≤ a - b + b :=
    add_le_add_right h b
  rw [add_zero, sub_add_cancel] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_of_sub_nonneg -/

example {a b : Int} (h : 0 ≤ a - b) : b ≤ a := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h