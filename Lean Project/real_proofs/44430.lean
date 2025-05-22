import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {z : Int} (hz : z ≠ 0) : z.sign.natAbs = 1 := by
  rw [Int.natAbs_sign, if_neg hz]