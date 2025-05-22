import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h <;> (rename_i g; simp [g])