import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < b) : -b < -a := by
  have h1 : 0 < -a + b := by
    rw [←neg_add_self a]
    exact add_lt_add_right h (-a)
  have h2 : 0 + -b < -a + b + -b := by
    rw [zero_add]
    rw [←neg_add b ((-a) + b)]
    exact add_lt_add_right h1 (-b)
  rw [←neg_add_cancel_left (-a) b] at h2
  exact h2

/- ACTUAL PROOF OF Int.neg_lt_neg -/

example {a b : Int} (h : a < b) : -b < -a := by
  have : 0 < -a + b := Int.add_left_neg a ▸ Int.add_lt_add_left h (-a)
  have : 0 + -b < -a + b + -b := Int.add_lt_add_right this (-b)
  rwa [Int.add_neg_cancel_right, Int.zero_add] at this