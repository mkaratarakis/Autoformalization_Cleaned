import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ b) : max a b = b := by
  rw [max_eq_right]
  exact h

/- ACTUAL PROOF OF Int.max_eq_right -/

example {a b : Int} (h : a ≤ b) : max a b = b := by
  simp [Int.max_def, h, Int.not_lt.2 h]