import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← ofNat_natAbs a, ← ofNat_natAbs a]
  rw [ofNat_mul]
  rw [Int.natAbs_mul_natAbs_self]
  rfl

/- ACTUAL PROOF OF Int.natAbs_mul_self' -/

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]