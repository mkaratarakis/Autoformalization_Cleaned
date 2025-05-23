import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  by_cases h1: 0 ≤ a
  · by_cases h2: 0 ≤ b
    · -- Case 1: a and b are both non-negative integers
      have a_eq : a = ofNat (natAbs a) := by simp [h1]
      have b_eq : b = ofNat (natAbs b) := by simp [h2]
      rw [a_eq, b_eq, Int.mul_ofNat_ofNat, natAbs_ofNat]
      simp
    · -- Case 2: a is non-negative and b is negative
      have a_eq : a = ofNat (natAbs a) := by simp [h1]
      have b_eq : b = -ofNat (natAbs b) := by simp [h2]
      rw [a_eq, b_eq, Int.mul_ofNat_neg_ofNat, natAbs_neg_ofNat]
      simp
  · by_cases h2: 0 ≤ b
    · -- Case 3: a is negative and b is non-negative
      have a_eq : a = -ofNat (natAbs a) := by simp [h1]
      have b_eq : b = ofNat (natAbs b) := by simp [h2]
      rw [a_eq, b_eq, Int.neg_ofNat_mul_ofNat, natAbs_neg_ofNat]
      simp
    · -- Case 4: a and b are both negative
      have a_eq : a = -ofNat (natAbs a) := by simp [h1]
      have b_eq : b = -ofNat (natAbs b) := by simp [h2]
      rw [a_eq, b_eq, Int.neg_ofNat_mul_neg_ofNat, natAbs_neg_ofNat]
      simp

/- ACTUAL PROOF OF Int.natAbs_mul -/

example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]