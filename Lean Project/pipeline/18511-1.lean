import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  constructor
  · exact hf.1
  · intros x hx y hy a b ha hb hab
    specialize hf.2 hx hy ha hb hab
    specialize hg.2 hx hy ha hb hab
    calc
      a • f x + b • f y + a * b * φ ‖x - y‖ + (a • g x + b • g y + a * b * ψ ‖x - y‖)
        ≤ f (a • x + b • y) + (g (a • x + b • y)) : by linarith [hf.2, hg.2]
      _ = (f + g) (a • x + b • y) : rfl

6. **Error Message and Proof State**
There is no error message and proof state provided.

/- ACTUAL PROOF OF UniformConcaveOn.add -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)