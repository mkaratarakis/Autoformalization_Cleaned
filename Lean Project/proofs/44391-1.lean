import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ c) : b ≤ -a + c := by
  have h1 : -a + (a + b) ≤ -a + c := by
    apply add_le_add_left
    exact h
  rw [neg_add_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_neg_add_of_add_le -/

example {a b c : Int} (h : a + b ≤ c) : b ≤ -a + c := by
  have h := Int.add_le_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h