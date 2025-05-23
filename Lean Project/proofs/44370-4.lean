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
  · have h₁ : a = ofNat (Nat.ofInt a) := by
      apply Int.ofNat_eq_coe
      exact h
    rw [h₁]
    rw [Int.toNat_of_nonneg (by simp [h])]
    rfl

/- ACTUAL PROOF OF Int.toNat_of_nonneg -/

example {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [toNat_eq_max, Int.max_eq_left h]