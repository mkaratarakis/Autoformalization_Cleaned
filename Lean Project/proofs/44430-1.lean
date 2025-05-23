import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  -- Since `z ≠ 0`, the sign of `z` is either 1 or -1.
  -- The absolute value of the sign of `z` is therefore 1.
  rw [sign_eq_of_ne_zero hz]
  -- Now, we need to show that `natAbs 1 = 1`.
  rw [natAbs_of_nonneg (by decide : (0 : Int) ≤ 1)]
  -- This simplifies to `1 = 1`, which is trivially true.
  rfl

/- ACTUAL PROOF OF Int.natAbs_sign_of_nonzero -/

example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]