import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.LogDeriv


open Filter Function
open scoped Topology BigOperators Classical
variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  by_cases hx : x = 0
  · simp [hx]
  · have h₁ : ∀ᵐ y ∂ (λ y, y ^ n), x = (fun y => (n : 𝕜) * y ^ (n - 1 : ℤ)) x := by
      exact deriv_zpow n x
    simp
    rw [h₁.logDeriv_apply]
    simp
    have h₂ : x ^ n = x * x ^ (n - 1) := by
      rw [zpow_add₀ hx]
      simp
    rw [h₂]
    simp
    ring_nf
    exact  hx

/- ACTUAL PROOF OF logDeriv_zpow -/

example (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]