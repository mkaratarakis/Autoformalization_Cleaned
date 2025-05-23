import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  calc
    a + b ≤ a + (-a + c) := by apply add_le_add_left (by apply le_of_eq; rfl)
    _ = c := by rw [add_left_neg, zero_add]

/- ACTUAL PROOF OF Int.add_le_of_le_neg_add -/

example {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h