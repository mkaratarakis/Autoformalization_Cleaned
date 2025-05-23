import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h1 : a ≤ b + c + c - c := by
    exact h
  rw [add_sub_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_add_of_sub_right_le -/

example {a b c : Int} (h : a - c ≤ b) : a ≤ b + c := by
  have h := Int.add_le_add_right h c
  rwa [Int.sub_add_cancel] at h