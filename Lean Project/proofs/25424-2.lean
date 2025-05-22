import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with
  | isTrue hp =>
    -- Case 1: p is true
    simp [decide]
    apply Iff.intro
    · intro h
      apply False.elim h
    · intro h
      apply h hp
  | isFalse hp =>
    -- Case 2: p is false
    simp [decide]
    apply Iff.intro
    · intro h
      exact h.symm
    · intro h
      exact h.symm

/- ACTUAL PROOF OF false_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]