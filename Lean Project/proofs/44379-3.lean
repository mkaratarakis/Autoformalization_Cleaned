import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : a ≤ toNat a := by
  unfold toNat
  split
  · intro n
    apply le_of_eq
    rfl
  · intro a
    exact le_of_lt (negSucc_lt_zero a)

/- ACTUAL PROOF OF Int.self_le_toNat -/

example (a : Int) : a ≤ toNat a := by
  rw [toNat_eq_max]; apply Int.le_max_left