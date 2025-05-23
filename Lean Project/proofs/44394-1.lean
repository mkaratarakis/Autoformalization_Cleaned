import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a ≤ c - b) : a + b ≤ c := by
  have h1 : a + b ≤ (c - b) + b := add_le_add_right h b
  rw [add_sub_cancel] at h1
  exact h1

/- ACTUAL PROOF OF Int.add_le_of_le_sub_right -/

example {a b c : Int} (h : a ≤ c - b) : a + b ≤ c := by
  have h := Int.add_le_add_right h b
  rwa [Int.sub_add_cancel] at h