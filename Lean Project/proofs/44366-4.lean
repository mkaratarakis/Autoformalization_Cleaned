import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
cases ha
· case inl ha =>
    exact Int.mul_nonpos_of_nonpos_of_nonneg ha (Int.le_trans h (Int.le_of_not_lt zero_le_one))
· case inr ha =>
    rw [neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
    exact Int.mul_le_mul_left h (Int.nonneg_of_pos ha)

/- ACTUAL PROOF OF Int.mul_le_mul_of_nonpos_left -/

example {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha