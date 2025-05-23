import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  by_cases h1: 0 ≤ a
  · by_cases h2: 0 ≤ b
    · -- Case 1: a and b are both non-negative integers
      have a_eq : a = ofNat (natAbs a) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h1
      have b_eq : b = ofNat (natAbs b) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h2
      rw [a_eq, b_eq]
      simp [natAbs_ofNat, Int.ofNat_mul]
    · -- Case 2: a is non-negative and b is negative
      have a_eq : a = ofNat (natAbs a) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h1
      have b_eq : b = -ofNat (natAbs b - 1) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h2
      rw [a_eq, b_eq]
      simp [natAbs_ofNat, Int.ofNat_mul, Int.negOfNat_neg]
  · by_cases h2: 0 ≤ b
    · -- Case 3: a is negative and b is non-negative
      have a_eq : a = -ofNat (natAbs a - 1) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h1
      have b_eq : b = ofNat (natAbs b) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h2
      rw [a_eq, b_eq]
      simp [natAbs_ofNat, Int.ofNat_mul, Int.negOfNat_neg]
    · -- Case 4: a and b are both negative
      have a_eq : a = -ofNat (natAbs a - 1) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h1
      have b_eq : b = -ofNat (natAbs b - 1) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h2
      rw [a_eq, b_eq]
      simp [natAbs_ofNat, Int.ofNat_mul, Int.negOfNat_neg]

/- ACTUAL PROOF OF Int.natAbs_mul -/

example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]