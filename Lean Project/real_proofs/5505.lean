import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example [h : Decidable p] :
    ite p True q ↔ ¬p → q := by
  cases h <;> (rename_i g; simp [g])