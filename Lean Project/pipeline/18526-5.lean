import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConvexOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  constructor
  · exact hf.left
  intros x hx y hy a b ha hb hab
  calc
    (f + g) (a • x + b • y) = f (a • x + b • y) + g (a • x + b • y) := rfl
    _ ≤ a • f x + b • f y - a * b * φ ‖x - y‖ + (a • g x + b • g y - a * b * ψ ‖x - y‖) :=
      add_le_add (hf.right hx hy ha hb hab) (hg.right hx hy ha hb hab)
    _ = a • f x + b • f y + a • g x + b • g y - a * b * (φ ‖x - y‖ + ψ ‖x - y‖) := by ring
    _ = a • (f x + g x) + b • (f y + g y) - a * b * (φ + ψ) ‖x - y‖ := by
      rw [add_sub_assoc]
      ring

/- ACTUAL PROOF OF UniformConvexOn.add -/

example (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)