import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) : logDeriv id x = 1 / x := by
  rw [logDeriv_apply]
  simp only [deriv_id, id.def]
  rw [one_div]
  exact (inv_eq_one_div x).symm

/- ACTUAL PROOF OF logDeriv_id -/

example (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]