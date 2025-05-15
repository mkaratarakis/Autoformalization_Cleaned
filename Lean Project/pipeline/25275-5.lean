import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  intro h
  apply Iff.intro
  · intro hb
    by_cases hb' : h = true
    · exact hb'
    · have hb'' : h = false := by
        cases h
        · contradiction
        · exact rfl
      contradiction
  · intro hb
    rw [hb]
    exact false_ne_true

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide