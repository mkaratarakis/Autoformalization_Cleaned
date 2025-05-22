import Init.PropLemmas
import Init.Classical

open Classical


example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  by_cases h : ∀ a, ¬ P a
  · exact Or.inr h
  · have h' := by
      apply not_not.mp
      intro hnp
      apply h
      intro a
      apply hnp
      exact a
    exact Or.inl h'

/- ACTUAL PROOF OF Classical.exists_or_forall_not -/

example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _