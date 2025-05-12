import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  intros x hx y hy a b hab
  calc
    a * (f + g) x + b * (f + g) y + a * b * (φ + ψ) (norm (x - y))
    _ = a * f x + b * f y + a * b * φ (norm (x - y)) + a * g x + b * g y + a * b * ψ (norm (x - y)) := by ring
    _ ≤ f (a * x + b * y) + g (a * x + b * y) := by apply add_le_add (hf x hx y hy a b hab) (hg x hx y hy a b hab)
    _ = (f + g) (a * x + b * y) := rfl

/- ACTUAL PROOF OF UniformConcaveOn.add -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)