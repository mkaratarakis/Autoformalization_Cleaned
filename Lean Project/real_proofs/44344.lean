import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (h : 0 ≤ b) : a ≤ a + b := by
  have : a + b ≥ a + 0 := Int.add_le_add_left h a
  rwa [Int.add_zero] at this