import Init.BinderPredicates
example
example : {b : Bool} → b ≠ false ↔ b = true := by
  apply Iff.intro
  · intro h
    cases b
    · exfalso; apply h; rfl
    · rfl
  · intro h
    rw [h]
    exact Ne.symm (Ne.refl true)

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide