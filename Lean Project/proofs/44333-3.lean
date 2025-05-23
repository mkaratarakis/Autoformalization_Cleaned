import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : b ≤ a) : min a b = b := by
  cases h' : min a b with c
  · simp at h'
    exfalso
    exact not_le_of_lt h' h
  · rfl

/- ACTUAL PROOF OF Int.min_eq_right -/

example {a b : Int} (h : b ≤ a) : min a b = b := by
  rw [Int.min_comm a b]; exact Int.min_eq_left h