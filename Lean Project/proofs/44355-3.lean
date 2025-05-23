import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : b < a) : 0 < a - b := by
  have h₁ : b + (-b) < a + (-b) :=
    add_lt_add_right h (-b)
  rw [add_right_neg, add_zero] at h₁
  exact h₁

/- ACTUAL PROOF OF Int.sub_pos_of_lt -/

example {a b : Int} (h : b < a) : 0 < a - b := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h