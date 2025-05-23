import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h1 : a ≤ b + c + c - c := by
    calc
      a ≤ b + c := h
      _ ≤ b + c + c - c := by
        rw [add_assoc]
        rw [add_sub_cancel_right]
  exact h1

/- ACTUAL PROOF OF Int.le_add_of_sub_right_le -/

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h