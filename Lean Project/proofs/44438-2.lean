import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  by_cases h : 0 ≤ a
  · rw [natAbs_of_nonneg h]
    simp
  · rw [natAbs_of_neg _]
    · rw [neg_mul_neg_eq_mul]
      simp
    · linarith

/- ACTUAL PROOF OF Int.natAbs_mul_self' -/

example (a : Int) : (natAbs a * natAbs a : Int) = a * a := by
  rw [← Int.ofNat_mul, natAbs_mul_self]