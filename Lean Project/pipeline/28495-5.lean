import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open NNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · push_neg at hx
    rw [NNReal.coe_rpow, Real.rpow_def_of_nonneg (NNReal.coe_nonneg x)]
    simp [hx, Ne.def, not_false_iff, and_true_iff]
    constructor
    · rintro rfl
      exact hy
    · exact id

/- ACTUAL PROOF OF NNReal.rpow_eq_zero_iff -/

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2