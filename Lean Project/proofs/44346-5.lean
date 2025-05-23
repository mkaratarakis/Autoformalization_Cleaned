import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 < a) : -a < 0 := by
  have h₁ : 0 < -a + a := by
    convert h using 1
    rw [add_comm]
    rfl
  simpa using h₁

/- ACTUAL PROOF OF Int.neg_neg_of_pos -/

example {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this