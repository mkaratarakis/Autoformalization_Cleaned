import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have h1 : 0 * b < a * b := Int.mul_lt_mul_of_neg_left ha hb
  rw [zero_mul] at h1
  exact h1

/- ACTUAL PROOF OF Int.mul_pos_of_neg_of_neg -/

example {a b : Int} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := Int.mul_lt_mul_of_neg_right ha hb
  rwa [Int.zero_mul] at this