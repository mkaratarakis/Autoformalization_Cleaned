import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p q True ↔ p → q := by
  cases h
  · intro hnp
    simp [hnp]
    exact Iff.intro (by simp) (by simp)
  · intro hp
    simp [hp]
    exact Iff.intro (by simp) (by simp)

/- ACTUAL PROOF OF if_true_right -/

example [h : Decidable p] :
    ite p q True ↔ p → q := by
  cases h <;> (rename_i g; simp [g])