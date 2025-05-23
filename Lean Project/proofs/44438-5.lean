import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  by_cases h : 0 ≤ a
  · rw [natAbs_of_nonneg h]
    simp
  · have : natAbs a = natAbs (-a) := by simp [natAbs, h]
    rw [this]
    simp

/- ACTUAL PROOF OF Int.natAbs_mul_self' -/

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]