import Init.PropLemmas
import Init.Classical

open Classical



example (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _