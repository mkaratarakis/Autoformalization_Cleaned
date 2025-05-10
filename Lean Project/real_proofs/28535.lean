import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open ENNReal
open scoped Classical
open Real NNReal ENNReal ComplexConjugate
open Finset Function Set
variable {w x y z : ℝ}


example (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_pos _)]
  · simp [coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]