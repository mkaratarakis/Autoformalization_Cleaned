import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p q True ↔ p → q := by
  cases h
  · simp [Iff]
    intro hnp
    apply True.intro
  · simp [Iff]
    intro hp
    apply hp

/- ACTUAL PROOF OF if_true_right -/

example [h : Decidable p] :
    ite p q True ↔ p → q := by
  cases h <;> (rename_i g; simp [g])