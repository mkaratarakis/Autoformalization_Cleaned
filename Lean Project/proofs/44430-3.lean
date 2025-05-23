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
    simp only [sign_of_pos, natAbs_of_nat_eq]
    rfl
  · -- If z is not positive
    simp only [sign_of_neg_of_ne_zero hz, natAbs_of_nat_eq]
    rfl

/- ACTUAL PROOF OF Int.natAbs_sign_of_nonzero -/

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]