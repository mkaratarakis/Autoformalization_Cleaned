import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ b) : min a b = a := by
  apply Int.min_eq_left
  assumption

/- ACTUAL PROOF OF Int.min_eq_left -/

example {a b : Int} (h : a ≤ b) : min a b = a := by
  simp [Int.min_def, h]