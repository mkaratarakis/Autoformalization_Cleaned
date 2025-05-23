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
    rw [Int.sign_eq_one_of_pos h]
    rfl
  · -- If z is not positive
    rw [Int.sign_eq_neg_one_of_nonpos h]
    rfl

/- ACTUAL PROOF OF Int.natAbs_sign_of_nonzero -/

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]