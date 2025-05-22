import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h with
  | isTrue hp =>
    simp [hp]
    exact iff_of_false (by simp [hp]) (by simp [hp])
  | isFalse hp =>
    simp [hp]
    exact iff_of_true (by simp [hp]) (by simp [hp])

/- ACTUAL PROOF OF if_false_left -/

example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h <;> (rename_i g; simp [g])