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
    have hg' := hg.2 hx hy ha hb hab
    have hf' := hf.2 hx hy ha hb hab
    calc
      a • (f - g) x + b • (f - g) y + a * b * (φ + ψ) ‖x - y‖
        = a • f x + b • f y - a • g x - b • g y + a * b * φ ‖x - y‖ + a * b * ψ ‖x - y‖ : by rw [sub_smul, sub_smul, Pi.sub_apply, Pi.sub_apply]
      _ ≤ a • f x + b • f y - (a • g x + b • g y - a * b * ψ ‖x - y‖) + a * b * φ ‖x - y‖ : by exact add_le_add_left hg' _
      _ = a • f x + b • f y + a * b * φ ‖x - y‖ - (a • g x + b • g y - a * b * ψ ‖x - y‖) : by rw [add_comm (a • f x + b • f y), add_assoc]
      _ ≤ f (a • x + b • y) - g (a • x + b • y) : by exact add_le_add_right hf' _
      _ = (f - g) (a • x + b • y) : by rw [Pi.sub_apply, Pi.sub_apply]

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg