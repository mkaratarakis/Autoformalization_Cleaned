import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : b ≤ c - a) : a + b ≤ c := by
  have h1 : a + b ≤ a + (c - a) := add_le_add_left h a
  rw [←add_assoc, add_comm a c, add_left_neg, add_zero] at h1
  exact h1

/- ACTUAL PROOF OF Int.add_le_of_le_sub_left -/

example {a b c : Int} (h : b ≤ c - a) : a + b ≤ c := by
  have h := Int.add_le_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h