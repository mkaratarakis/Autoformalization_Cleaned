import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext1 x
  rw [logDeriv_apply]
  simp [deriv_const]
  rw [zero_div]

/- ACTUAL PROOF OF logDeriv_const -/

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]