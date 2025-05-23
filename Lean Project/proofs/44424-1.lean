import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [add_comm] at h
  apply Int.add_lt_add_iff_left
  exact h

/- ACTUAL PROOF OF Int.lt_add_of_neg_add_lt_right -/

example {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h