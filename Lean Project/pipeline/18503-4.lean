import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  constructor
  · exact hf.1
  · intros x hx y hy a b ha hb hab
    have h1 : a • (f - g) x + b • (f - g) y + a * b * (φ + ψ) ‖x - y‖
      = (a • f x + b • f y + a * b * φ ‖x - y‖) - (a • g x + b • g y)
    {simp [sub_smul, smul_sub]}
    have h2 : (a • f x + b • f y + a * b * φ ‖x - y‖) - (a • g x + b • g y)
      ≤ f (a • x + b • y) - (a • g x + b • g y + a * b * ψ ‖x - y‖)
    {apply hf.2 hx hy ha hb hab}
    have h3 : f (a • x + b • y) - (a • g x + b • g y + a * b * ψ ‖x - y‖)
      ≤ (f - g) (a • x + b • y)
    {apply hg.2 hx hy ha hb hab}
    exact h3.trans h2.trans h1

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg