import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_apply]
  convert (deriv_zpow n x).symm using 1
  rw [mul_div_cancel_left _ (zpow_ne_zero _ (differentiableAt_zpow.mp (by simp [x.ne_zero_iff])))].

/- ACTUAL PROOF OF logDeriv_zpow -/

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]