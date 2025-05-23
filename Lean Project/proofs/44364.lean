import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have h₃ : 0 < b - a :=
    Int.sub_pos_of_lt h₁
  have h₄ : 0 < (b - a) * c :=
    Int.mul_pos h₃ h₂
  have h₅ : 0 < b * c - a * c := by
    rw [← Int.sub_mul]
    exact h₄
  exact Int.lt_of_sub_pos h₅

/- ACTUAL PROOF OF Int.mul_lt_mul_of_pos_right -/

example {a b c : Int}
  (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  have : 0 < b - a := Int.sub_pos_of_lt h₁
  have : 0 < (b - a) * c := Int.mul_pos this h₂
  rw [Int.sub_mul] at this
  exact Int.lt_of_sub_pos this