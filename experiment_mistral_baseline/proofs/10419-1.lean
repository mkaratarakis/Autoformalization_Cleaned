import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) : logDeriv id x = 1 / x := by
  unfold logDeriv
  simp [deriv_id, id x]
  rw [div_eq_inv_mul]
  norm_num

/- ACTUAL PROOF OF logDeriv_id -/

example (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]