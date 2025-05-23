import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := by
    apply Int.mul_lt_mul_of_pos_right
    exact ha
    exact hb
  rwa [mul_zero] at h

/- ACTUAL PROOF OF Int.mul_neg_of_neg_of_pos -/

example {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h