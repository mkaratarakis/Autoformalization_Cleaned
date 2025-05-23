import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b < a + c) : b < c := by
  have h₁ : -a + (a + b) < -a + (a + c) := by
    apply Int.add_lt_add_left
    . exact h
    . simp
  simp at h₁
  exact h₁

/- ACTUAL PROOF OF Int.lt_of_add_lt_add_left -/

example {a b c : Int} (h : a + b < a + c) : b < c := by
  have : -a + (a + b) < -a + (a + c) := Int.add_lt_add_left h _
  simp [Int.neg_add_cancel_left] at this
  assumption