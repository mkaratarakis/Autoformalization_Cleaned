import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
apply Int.mul_le_mul_of_nonpos_left h ha

/- ACTUAL PROOF OF Int.mul_le_mul_of_nonpos_left -/

example {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha