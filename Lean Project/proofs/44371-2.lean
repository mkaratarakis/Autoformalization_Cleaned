import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) {b : Int} (h : 0 < b) : a < a + b := by
  have step1 : a + 0 < a + b := by
    apply add_lt_add_left
    exact h
  rw [zero_add] at step1
  exact step1

/- ACTUAL PROOF OF Int.lt_add_of_pos_right -/

example (a : Int) {b : Int} (h : 0 < b) : a < a + b := by
  have : a + 0 < a + b := Int.add_lt_add_left h a
  rwa [Int.add_zero] at this