import Init.Core
import Init.SimpLemmas




example {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
    (h₁ : p₁ = p₂)
    (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
    : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a) := by
  subst h₁
  funext a
  exact (h₂ a).symm

/- ACTUAL PROOF OF forall_prop_domain_congr -/

example {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
    (h₁ : p₁ = p₂)
    (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
    : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a) := by
  subst h₁; simp [← h₂]