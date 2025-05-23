import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have h1 : -a ≤ -0 := neg_nonneg_of_nonneg h
  rw [neg_zero] at h1
  exact h1

/- ACTUAL PROOF OF Int.neg_nonpos_of_nonneg -/

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this