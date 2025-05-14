import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open ENNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}

example (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · -- Case 1: x = ∞
    simp [ENNReal.top_rpow_of_pos]
    exact le_top
  · -- Case 2: x is a non-negative real number
    simp [ENNReal.some_rpow_of_nonneg (le_of_lt (zero_lt_one' ℝ))]
    exact le_rfl

/- ACTUAL PROOF OF ENNReal.rpow_one -/

example (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_lt