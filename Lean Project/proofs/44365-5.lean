import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < b) : -b < -a := by
  have h1 : 0 < -a + b := by
    rw [Int.neg_add_cancel_left a a]
    exact Int.add_lt_add_right h (Int.neg a)
  have h2 : -b < -a + b + -b := by
    rw [Int.add_comm (-b) 0]
    rw [← Int.add_assoc (-b) (-a + b)]
    exact Int.add_lt_add_right h1 (-b)
  rw [Int.add_assoc, Int.add_left_neg, Int.zero_add] at h2
  exact h2

/- ACTUAL PROOF OF Int.neg_lt_neg -/

example {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this