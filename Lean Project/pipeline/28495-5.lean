import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open NNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  constructor
  · intro h
    rw [NNReal.coe_rpow, Real.rpow_eq_zero_iff_of_nonneg x.2] at h
    rcases h with ⟨hx, hy⟩
    exact ⟨NNReal.coe_eq_zero.1 hx, hy⟩
  · rintro ⟨rfl, hy⟩
    rw [NNReal.coe_zero, Real.zero_rpow hy, NNReal.coe_eq_zero]

/- ACTUAL PROOF OF NNReal.rpow_eq_zero_iff -/

example {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2