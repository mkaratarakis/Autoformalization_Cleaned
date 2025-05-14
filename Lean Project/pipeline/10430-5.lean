import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x :=
  if h : x = 0 then by simp [h]
  else
    if hn : n = 0 then by simp [hn]
    else
      calc
        logDeriv (· ^ n) x = deriv (· ^ n) x / (x ^ n) := logDeriv_apply _ _
        _ = ((n : 𝕜) * x ^ (n - 1)) / (x ^ n) := by rw [deriv_zpow]
        _ = (n : 𝕜) / x := by field_simp [zpow_ne_zero h]
        _

/- ACTUAL PROOF OF logDeriv_zpow -/

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]