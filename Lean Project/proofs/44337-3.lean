import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ b) : max a b = b := by
  unfold max
  cases le_total a b with
  | inl h => rw [if_pos h]
  | inr h => rw [if_neg h]
  exact h

/- ACTUAL PROOF OF Int.max_eq_right -/

example {a b : Int} (h : a ≤ b) : max a b = b := by
  simp [Int.max_def, h, Int.not_lt.2 h]