import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  have : deriv (fun _ : 𝕜 ↦ a) = 0 := by {
    intro x
    simp only [deriv_const]
  }
  simp only [logDeriv, Pi.zero_apply, div_zero]
  rw [this]

/- ACTUAL PROOF OF logDeriv_const -/

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]