import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  refine ⟨hf.1.inter hg.1, fun x hx y hy a b ha hb hab ↦ _⟩
  rw [sub_le_iff_le_add', Pi.sub_apply, Pi.sub_apply]
  exact add_le_add
      (hf.2 hx hy ha hb hab)
      ((hg.2 hx hy ha hb hab).symm.trans (neg_le_neg (le_of_eq (mul_one _).symm)))

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg