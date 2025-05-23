import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < b) : -b < -a := by
  have h1 : 0 < -a + b := by
    apply add_lt_add_left
    exact h
  have h2 : 0 + -b < -a + b + -b := by
    apply add_lt_add_left
    exact h1
  rw [add_assoc, add_left_neg, zero_add] at h2
  exact h2

/- ACTUAL PROOF OF Int.neg_lt_neg -/

example {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this