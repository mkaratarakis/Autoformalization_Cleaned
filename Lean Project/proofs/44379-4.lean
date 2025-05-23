import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : a ≤ toNat a := by
  unfold toNat
  split
  · intro
    rfl
  · intro a'
    exact negSucc_le_zero a'

/- ACTUAL PROOF OF Int.self_le_toNat -/

example (a : Int) : a ≤ toNat a := by
  rw [toNat_eq_max]; apply Int.le_max_left