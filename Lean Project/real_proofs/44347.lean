import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b c : Int} (h : a + b ≤ a + c) : b ≤ c := by
  have : -a + (a + b) ≤ -a + (a + c) := Int.add_le_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption