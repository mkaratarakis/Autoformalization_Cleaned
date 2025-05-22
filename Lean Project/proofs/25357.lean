import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by
  intros a b
  apply Iff.intro
  . intro h
    cases a <;> cases b <;> simp at h <;> simp [h]
    all_goals {
      cases h
    }
  . intro h
    cases a <;> cases b <;> simp [h]
    repeat {
      contradiction
    }

/- ACTUAL PROOF OF Bool.not_not_eq -/

example : ∀ {a b : Bool}, ¬(!a) = b ↔ a = b := by
  decide