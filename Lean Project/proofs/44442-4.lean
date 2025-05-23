import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  constructor
  · intro h
    by_cases h1: a = n
    · simp [h1]
    · have h2: a = -n := by
        apply natAbs_eq
        exact h
        exact h1
      simp [h2]
  · intro h
    by_cases h1: a - n = 0
    · have h2: a = n := by
        linarith
      rw [h2]
      exact natAbs_of_nat _
    · have h3: a + n = 0 := by
        linarith
      have h4: a = -n := by
        linarith
      rw [h4]
      exact natAbs_of_nat _
    · have h3 : a + n = 0 := by
        linarith
      have h4 : a = -n := by
        linarith
      rw [h4]
      exact natAbs_of_nat _

/- ACTUAL PROOF OF Int.eq_natAbs_iff_mul_eq_zero -/

example : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  rw [natAbs_eq_iff, Int.mul_eq_zero, ← Int.sub_neg, Int.sub_eq_zero, Int.sub_eq_zero]