import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ _⟩
  specialize hf.2 hx hy ha hb hab
  specialize hg.2 hx hy ha hb hab
  calc
    a • (f - g) x + b • (f - g) y + a * b * (φ + ψ) ‖x - y‖
      = a • f x + b • f y + a * b * φ ‖x - y‖ - a • g x - b • g y + a * b * ψ ‖x - y‖ := by simp [sub_eq_add_neg]
    _ ≤ f (a • x + b • y) - g (a • x + b • y) := by linarith
    _ = (f - g) (a • x + b • y) := rfl

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg