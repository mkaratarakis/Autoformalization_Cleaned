import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -c + a ≤ b) : a ≤ b + c := by
  have h1 := add_le_add_left h c
  exact h1

/- ACTUAL PROOF OF Int.le_add_of_neg_add_le_right -/

example {a b c : Int} (h : -c + a ≤ b) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_right_le h