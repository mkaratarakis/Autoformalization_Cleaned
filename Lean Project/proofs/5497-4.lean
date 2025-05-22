import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h with
  | isTrue hp =>
    simp [hp]
    apply Iff.intro
    · intro hn
      contradiction
    · intro hn
      contradiction
  | isFalse hp =>
    simp [hp]
    apply Iff.intro
    · intro h
      exact ⟨hp, h⟩
    · intro h
      exact h.right

/- ACTUAL PROOF OF if_false_left -/

example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h <;> (rename_i g; simp [g])