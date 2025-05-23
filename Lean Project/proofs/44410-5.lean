import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [add_comm b c] at h
  exact Int.le_sub_comm.2 h

/- ACTUAL PROOF OF Int.neg_add_le_right_of_le_add -/

example {a b c : Int} (h : a ≤ b + c) : -c + a ≤ b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_le_left_of_le_add h