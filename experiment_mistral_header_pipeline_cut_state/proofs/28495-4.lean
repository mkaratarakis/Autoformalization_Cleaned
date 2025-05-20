import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open NNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [NNReal.coe_rpow, Real.rpow_eq_zero_iff_of_nonneg x.2]
  constructor
  · rintro rfl hy
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hy⟩
    exact NNReal.coe_eq_zero.2 (zero_rpow hy)

/- ACTUAL PROOF OF NNReal.rpow_eq_zero_iff -/

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2