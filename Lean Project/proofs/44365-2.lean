import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < b) : -b < -a := by
  have h1 : 0 < -a + b := by
    have h2 : a + -a = 0 := by rw [add_left_neg]
    rw [← h2]
    exact add_lt_add_right h (-a)
  have h3 : 0 + -b < -a + b + -b := by
    rw [add_comm (-b) 0]
    rw [← add_assoc (-b) (-a + b)]
    exact add_lt_add_right h1 (-b)
  rw [add_assoc, add_left_neg, zero_add] at h3
  exact h3

/- ACTUAL PROOF OF Int.neg_lt_neg -/

example {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this