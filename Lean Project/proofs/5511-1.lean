import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then p else q) = (¬p → q) := by
  cases h with
  | isTrue g =>
    calc
      (if p then p else q) = p := by rfl
      _ = (¬p → q) := by
        simp [g]
        exact propext (Iff.intro (fun hnp => False.elim (hnp g)) (fun hq => hq))
  | isFalse g =>
    calc
      (if p then p else q) = q := by rfl
      _ = (¬p → q) := by
        simp [g]
        exact propext (Iff.intro (fun hnp => True.intro) (fun hq => hq))

/- ACTUAL PROOF OF ite_true_same -/

example (p q : Prop) [h : Decidable p] : (if p then p else q) = (¬p → q) := by
  cases h <;> (rename_i g; simp [g])