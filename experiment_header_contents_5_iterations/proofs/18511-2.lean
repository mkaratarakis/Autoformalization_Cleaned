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
    have h1 : 0 ≤ a := ha
    have h2 : 0 ≤ b := hb
    have h3 : a + b = 1 := hab
    apply add_le_add
    · exact hf.2 hx hy h1 h2 h3
    · exact hg.2 hx hy h1 h2 h3

/- ACTUAL PROOF OF UniformConcaveOn.add -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)