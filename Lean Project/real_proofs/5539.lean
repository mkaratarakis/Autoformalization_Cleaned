import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example [h : Decidable p] :
    ite p q False ↔ p ∧ q := by
  cases h <;> (rename_i g; simp [g])