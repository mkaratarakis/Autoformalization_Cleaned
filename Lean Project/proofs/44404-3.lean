import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h1 : a + -b ≤ c := by rwa [add_comm] at h
  exact Int.add_le_add_left h1 b

/- ACTUAL PROOF OF Int.le_add_of_neg_add_le_left -/

example {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  rw [Int.add_comm] at h
  exact Int.le_add_of_sub_left_le h