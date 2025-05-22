import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example (p q : Prop) [h : Decidable p] : (if p then p else q) = (¬p → q) := by
  cases h <;> (rename_i g; simp [g])