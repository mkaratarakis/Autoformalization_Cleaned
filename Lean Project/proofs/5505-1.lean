import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p True q ↔ ¬p → q := by
  cases h
  · -- Case: p is false
    simp [ite_false, imp_false]
  · -- Case: p is true
    simp [ite_true, imp_true]

/- ACTUAL PROOF OF if_true_left -/

example [h : Decidable p] :
    ite p True q ↔ ¬p → q := by
  cases h <;> (rename_i g; simp [g])