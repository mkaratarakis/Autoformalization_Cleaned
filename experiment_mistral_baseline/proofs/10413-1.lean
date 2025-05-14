import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  intro x
  have h1 : HasStrictFDerivAt (fun x : 𝕜 ↦ a) (0 : 𝕜 →L[𝕜] 𝕜') x := by
    simp only [hasStrictFDerivAt_const]
  have h2 : fderiv 𝕜 (fun x : 𝕜 ↦ a) x = 0 := by
    simp only [fderiv_const]
  exact logDeriv_eq_fderiv_div h1 h2

/- ACTUAL PROOF OF logDeriv_const -/

example (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]