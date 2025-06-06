import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := by
    apply Int.mul_lt_mul_of_neg_left
    exact hb
    exact ha
  rw [Int.mul_zero] at h
  exact h

/- ACTUAL PROOF OF Int.mul_neg_of_pos_of_neg -/

example {a b : Int} (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := Int.mul_lt_mul_of_pos_left hb ha
  rwa [Int.mul_zero] at h