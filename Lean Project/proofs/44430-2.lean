import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  -- Since `z ≠ 0`, the sign of `z` is either 1 or -1.
  -- The absolute value of the sign of `z` is therefore 1.
  by_cases h : 0 < z
  · -- If z is positive
    have : z.sign = 1 := sign_of_pos _
    rw [this]
    exact natAbs_one.symm
  · -- If z is not positive
    have : z.sign = -1 := sign_of_neg _
    rw [this]
    exact natAbs_neg_one.symm

/- ACTUAL PROOF OF Int.natAbs_sign_of_nonzero -/

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]