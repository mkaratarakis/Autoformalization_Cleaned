import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open NNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [←NNReal.coe_eq_zero, NNReal.coe_rpow, Real.rpow_eq_zero_iff_of_nonneg (NNReal.coe_nonneg x)]
  simp [NNReal.coe_eq_zero]

/- ACTUAL PROOF OF NNReal.rpow_eq_zero_iff -/

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2