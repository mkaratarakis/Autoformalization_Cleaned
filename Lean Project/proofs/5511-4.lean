import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then p else q) = (¬p → q) := by
  cases h with
  | isTrue g =>
    calc
      (if p then p else q) = p := by rfl
      _ = (¬p → q) := by
        apply propext
        apply Iff.intro
        · intro hnp
          exfalso
          apply hnp
          exact g
        · intro hq
          exact hq
  | isFalse g =>
    calc
      (if p then p else q) = q := by rfl
      _ = (¬p → q) := by
        apply propext
        apply Iff.intro
        · intro hnp
          exact True.intro
        · intro hq
          exact hq

/- ACTUAL PROOF OF ite_true_same -/

example (p q : Prop) [h : Decidable p] : (if p then p else q) = (¬p → q) := by
  cases h <;> (rename_i g; simp [g])