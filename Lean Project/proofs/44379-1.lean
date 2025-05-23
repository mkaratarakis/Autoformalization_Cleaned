import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : a ≤ toNat a := by
  unfold toNat
  split
  · apply le_max_left
  · apply le_max_right
  · exact zero_le _

/- ACTUAL PROOF OF Int.self_le_toNat -/

example (a : Int) : a ≤ toNat a := by
  rw [toNat_eq_max]; apply Int.le_max_left