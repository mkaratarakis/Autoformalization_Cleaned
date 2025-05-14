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
    calc
      a • (f - g) x + b • (f - g) y + a * b * (φ + ψ) ‖x - y‖
        = a • f x + b • f y - a • g x - b • g y + a * b * φ ‖x - y‖ + a * b * ψ ‖x - y‖ : by rw [sub_smul, sub_smul, Pi.sub_apply, Pi.sub_apply]
      _ ≤ a • f x + b • f y - (a • g x + b • g y - a * b * ψ ‖x - y‖) + a * b * φ ‖x - y‖ : by apply add_le_add_left; exact hg.2 hx hy ha hb hab
      _ = a • f x + b • f y - a • g x - b • g y + a * b * φ ‖x - y‖ : by rw [sub_sub, sub_eq_add_neg, add_comm]
      _ ≤ f (a • x + b • y) - g (a • x + b • y) : by apply add_le_add_right; exact hf.2 hx hy ha hb hab
      _ = (f - g) (a • x + b • y) : by rw [Pi.sub_apply, Pi.sub_apply]

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg