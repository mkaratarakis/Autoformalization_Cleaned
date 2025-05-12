import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_apply, deriv_zpow]
  simp only [mul_div_assoc, Int.cast_inj]
  field_simp [zpow_ne_zero]
  rw [zpow_add₀, zpow_neg, inv_mul_cancel_left₀]
  { apply Ne.symm
    apply zpow_ne_zero }
  ring_nf
  norm_cast

/- ACTUAL PROOF OF logDeriv_zpow -/

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]