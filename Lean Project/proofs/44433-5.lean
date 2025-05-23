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
      rw [a_eq, b_eq, Int.ofNat_mul, natAbs_ofNat]
    · -- Case 2: a is non-negative and b is negative
      have a_eq : a = ofNat (natAbs a) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h1
      have b_eq : b = -ofNat (natAbs b) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h2
      rw [a_eq, b_eq, Int.ofNat_mul_negOfNat, natAbs_neg]
  · by_cases h2: 0 ≤ b
    · -- Case 3: a is negative and b is non-negative
      have a_eq : a = -ofNat (natAbs a) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h1
      have b_eq : b = ofNat (natAbs b) := by
        apply Int.ofNat_eq_coe
        exact natAbs_eq_of_nonneg h2
      rw [a_eq, b_eq, Int.negOfNat_mul_ofNat, natAbs_neg]
    · -- Case 4: a and b are both negative
      have a_eq : a = -ofNat (natAbs a) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h1
      have b_eq : b = -ofNat (natAbs b) := by
        apply Int.negOfNat_eq_neg_coe
        exact natAbs_eq_of_neg h2
      rw [a_eq, b_eq, Int.negOfNat_mul_negOfNat, natAbs_neg, natAbs_neg]

/- ACTUAL PROOF OF Int.natAbs_mul -/

example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]