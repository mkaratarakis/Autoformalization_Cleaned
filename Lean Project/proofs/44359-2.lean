import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  exact Int.mul_le_mul_of_nonneg_left h₁ h₂

/- ACTUAL PROOF OF Int.mul_le_mul_of_nonneg_right -/

example {a b c : Int}
    (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := by
  rw [Int.mul_comm, Int.mul_comm b]; exact Int.mul_le_mul_of_nonneg_left h₁ h₂