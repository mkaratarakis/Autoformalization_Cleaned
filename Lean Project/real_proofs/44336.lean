import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (h : a ≤ b) : min a b = a := by
  simp [Int.min_def, h]