import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a - b ≤ 0) : a ≤ b := by
  have h2 : a - b + b ≤ 0 + b :=
    add_le_add_right h b
  rw [sub_add_cancel, zero_add] at h2
  exact h2

/- ACTUAL PROOF OF Int.le_of_sub_nonpos -/

example {a b : Int} (h : a - b ≤ 0) : a ≤ b := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel, Int.zero_add] at h