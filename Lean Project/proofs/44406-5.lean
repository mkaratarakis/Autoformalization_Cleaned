import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h₁ : a + b < a + (-a + c) := by
    apply Int.add_lt_add_left
    exact h
  have h₂ : a + (-a + c) = c := by
    rw [add_assoc, add_neg_cancel_left]
  rw [h₂] at h₁
  exact h₁

/- ACTUAL PROOF OF Int.add_lt_of_lt_neg_add -/

example {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h