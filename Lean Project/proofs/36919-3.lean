import Init.PropLemmas
import Init.Classical

open Classical


example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  by_cases h : ∀ a, ¬ P a
  · exact Or.inr h
  · have h' := by
      push_neg h
      simp only [not_forall, not_not] at h
      exact h
    exact Or.inl h'

/- ACTUAL PROOF OF Classical.exists_or_forall_not -/

example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _