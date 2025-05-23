import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [sub_eq_add_neg]
  apply natAbs_add_le

/- ACTUAL PROOF OF Int.natAbs_sub_le -/

example (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
  rw [← Int.natAbs_neg b]; apply natAbs_add_le