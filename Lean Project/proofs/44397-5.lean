import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  calc
    b = b + 0 := by simp
    _ = b + (a + -a) := by rw [add_left_neg]
    _ = (b + a) + -a := by rw [add_assoc]
    _ ≤ c + -a := by
      apply Int.add_le_add_right
      exact h
    _ = c - a := by rfl

/- ACTUAL PROOF OF Int.le_sub_left_of_add_le -/

example {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h