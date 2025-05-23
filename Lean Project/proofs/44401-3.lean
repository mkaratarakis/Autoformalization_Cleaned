import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  have h' : a - b ≤ c := Int.sub_le_iff_le_add.mp h
  exact h'

/- ACTUAL PROOF OF Int.neg_add_le_left_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : -b + a ≤ c := by
  rw [Int.add_comm]
  exact Int.sub_left_le_of_le_add h