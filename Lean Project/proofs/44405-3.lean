import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b < c) : b < -a + c := by
  have h1 : -a + (a + b) < -a + c := by
    apply Int.add_lt_add_left
    exact h
  rw [←add_assoc, neg_add_cancel_left] at h1
  exact h1

/- ACTUAL PROOF OF Int.lt_neg_add_of_add_lt -/

example {a b c : Int} (h : a + b < c) : b < -a + c := by
  have h := Int.add_lt_add_left h (-a)
  rwa [Int.neg_add_cancel_left] at h