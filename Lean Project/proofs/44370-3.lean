import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [Int.toNat.eq_def]
  by_cases ha₀ : a = 0
  · rw [ha₀]
    rfl
  · rw [Int.ofNat_eq_coe]
    rw [Int.toNat_of_nonneg h]
    rw [Int.coe_nat_eq_coe_nat_iff]
    exact h

/- ACTUAL PROOF OF Int.toNat_of_nonneg -/

example {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [toNat_eq_max, Int.max_eq_left h]