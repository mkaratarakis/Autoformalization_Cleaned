import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := Int.mul_lt_mul_of_pos_right ha hb
  rwa [Int.zero_mul] at h