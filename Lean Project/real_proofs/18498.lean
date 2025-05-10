import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConvexOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}


example (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg