import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h1 : a ≤ b + c + c - c := by
    calc
      a := a
      _ ≤ b + c + c := by
        apply add_le_add_left
        apply le_of_sub_le_right
        exact h
      _ = b + c + c - c := by
        rw [add_sub_cancel']
  rw [add_sub_cancel'] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_add_of_sub_right_le -/

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h