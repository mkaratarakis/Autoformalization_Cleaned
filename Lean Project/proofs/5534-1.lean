import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h
  · -- Case 1: p is false
    have : ¬p := h
    have : ¬(p ∧ q) := by
      intro hpq
      apply this
      exact hpq.left
    apply propext
    exact iff_of_true (show ¬(p ∧ q) ↔ ¬p, from iff.rfl)
  · -- Case 2: p is true
    have : p := h
    have : p ∧ q ↔ q := by
      apply iff.intro
      · intro hpq
        exact hpq.right
      · intro hq
        exact ⟨this, hq⟩
    apply propext
    exact iff_of_true (show q ↔ p ∧ q)

/- ACTUAL PROOF OF ite_false_same -/

example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h <;> (rename_i g; simp [g])