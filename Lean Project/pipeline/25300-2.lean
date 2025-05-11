import Init.BinderPredicates
example (a ↔ b) := by
apply Iff.intro
· intro h
  cases b
  · left
    rfl
  · right
    rfl
· intro h
  cases h
  · left
    rfl
  · right
    rfl

/- ACTUAL PROOF OF Bool.eq_iff_iff -/

example {a b : Bool} : a = b ↔ (a ↔ b) := by
  cases b <;> simp