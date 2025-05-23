import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  have h1 : a ≤ c + b := by simp [Int.add_comm] at h; assumption
  exact Int.sub_le_iff_le_add.mp h1

/- ACTUAL PROOF OF Int.neg_add_le_right_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h