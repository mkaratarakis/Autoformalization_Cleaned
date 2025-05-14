import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strong

open UniformConcaveOn
open Real
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  unfold UniformConcaveOn
  unfold UniformConvexOn
  simp only [Pi.sub_apply, Function.comp]
  intros x y m hx hy hm
  specialize hf x y m hx hy hm
  specialize hg x y m hx hy hm
  simp only [neg_le_neg_iff] at hg
  calc
    m • (f - g) x + m • (f - g) y
      = m • f x - m • g x + m • f y - m • g y := by simp [Pi.sub_apply, smul_sub]
    _ ≤ m • f x + m • f y - (m • f + m • g) (m • x + m • y) - 2 * m * (1 - m) * ψ (∥x - y∥) := by linarith
    _ = (m • f + m • f) (m • x + m • y) - 2 * m * (1 - m) * (φ + ψ) (∥x - y∥) := by linarith
    _ = (m • (f - g) + m • (f - g)) (m • x + m • y) - 2 * m * (1 - m) * (φ + ψ) (∥x - y∥) := by linarith
qed

/- ACTUAL PROOF OF UniformConcaveOn.sub -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by
  simpa using hf.add hg.neg