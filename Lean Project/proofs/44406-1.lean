import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h₁ : a + b < a + (-a + c) := by
    rwa [add_right_comm, add_neg_cancel_left]
  rwa [add_right_comm, add_neg_cancel_left] at h₁

/- ACTUAL PROOF OF Int.add_lt_of_lt_neg_add -/

example {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h