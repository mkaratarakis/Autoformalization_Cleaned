import Init.PropLemmas
import Init.Classical

open Classical


example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  by_cases h : ∀ a, ¬ P a
  · exact Or.inr h
  · push_neg at h
    cases' h with a ha
    exact Or.inl ⟨a, ha⟩

/- ACTUAL PROOF OF Classical.exists_or_forall_not -/

example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _