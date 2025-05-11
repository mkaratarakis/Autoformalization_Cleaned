import Init.Data.Char.Lemmas
example (h : a < b) : a ≠ b := by
  intro h₁
  rw [h₁] at h
  apply Char.lt_irrefl _ h

/- ACTUAL PROOF OF String.ne_of_lt -/

example {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction