import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]