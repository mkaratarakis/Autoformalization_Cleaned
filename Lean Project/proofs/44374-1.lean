import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have h : 0 < c * (b - a) := by
    apply mul_pos
    · exact h₂
    · linarith
  calc
    c * b - c * a = c * (b - a) := by rw [mul_sub]
    _ > 0 := h

  linarith

/- ACTUAL PROOF OF Int.mul_lt_mul_of_pos_left -/

example {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  have : 0 < c * (b - a) := Int.mul_pos h₂ (Int.sub_pos_of_lt h₁)
  rw [Int.mul_sub] at this
  exact Int.lt_of_sub_pos this