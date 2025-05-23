import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have h1 : -a + (a + b) ≤ -a + (a + c) := by
    apply add_le_add_left
    exact h
  have h2 : -a + (a + b) = b := by
    simp
  have h3 : -a + (a + c) = c := by
    simp
  rw [h2, h3] at h1
  exact h1

/- ACTUAL PROOF OF Int.le_of_add_le_add_left -/

example {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption