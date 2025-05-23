import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h1 : a + b ≤ a + (-a + c) := add_le_add_left h a
  rw [add_assoc, ←add_neg_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.add_le_of_le_neg_add -/

example {a b c : Int} (h : b ≤ -a + c) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [Int.add_neg_cancel_left] at h