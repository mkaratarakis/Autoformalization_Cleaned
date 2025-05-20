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
        ≤ f (a • x + b • y) + (g (a • x + b • y)) :
        add_le_add hf.2 hg.2
      _ = (f + g) (a • x + b • y) : rfl

6. **Error Message and Proof State**

```
failed to prove
  ∀ (x_1 : E), x_1 ∈ s → ∀ (y_1 : E), y_1 ∈ s → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → a • f x_1 + b • f y_1 + a * b * (φ + ψ) ‖x_1 - y_1‖ ≤ f (a • x_1 + b • y_1)
⊢ ∀ (x_1 : E), x_1 ∈ s → ∀ (y_1 : E), y_1 ∈ s → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → a • f x_1 + b • f y_1 + a * b * (φ + ψ) ‖x_1 - y_1‖ ≤ f (a • x_1 + b • y_1)
```

We need to show that for any \( x, y \in s \) and any \( a, b \in \mathbb{R} \) such that \( 0 \leq a \), \( 0 \leq b \), and \( a + b = 1 \), the following inequality holds:
\[ a \cdot (f + g)(x) + b \cdot (f + g)(y) + a \cdot b \cdot (\varphi + \psi)(\|x - y\|) \leq (f + g)(a \cdot x + b \cdot y). \]

By the definition of `UniformConcaveOn`, we have:
\[ a \cdot f(x) + b \cdot f(y) + a \cdot b \cdot \varphi(\|x - y\|) \leq f(a \cdot x + b \cdot y), \]
\[ a \cdot g(x) + b \cdot g(y) + a \cdot b \cdot \psi(\|x - y\|) \leq g(a \cdot x + b \cdot y). \]

Adding these two inequalities, we get:
\[ a \cdot f(x) + b \cdot f(y) + a \cdot b \cdot \varphi(\|x - y\|) + a \cdot g(x) + b \cdot g(y) + a \cdot b \cdot \psi(\|x - y\|) \leq f(a \cdot x + b \cdot y) + g(a \cdot x + b \cdot y). \]

Using the distributive property of multiplication over addition and the commutativity of addition, we can rewrite the left-hand side as:
\[ a \cdot (f(x) + g(x)) + b \cdot (f(y) + g(y)) + a \cdot b \cdot (\varphi(\|x - y\|) + \psi(\|x - y\|)). \]

Thus, we have:
\[ a \cdot (f + g)(x) + b \cdot (f + g)(y) + a \cdot b \cdot (\varphi + \psi)(\|x - y\|) \leq (f + g)(a \cdot x + b \cdot y). \]

This completes the proof.
$\blacksquare$

/- ACTUAL PROOF OF UniformConcaveOn.add -/

example (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)