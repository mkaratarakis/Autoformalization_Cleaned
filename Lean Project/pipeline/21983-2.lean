import Init.Data.Char.Lemmas
example (h : a < b) : a ≠ b := by
  intro h₁
  rw [← h₁] at h
  exact Char.lt_irrefl a h

/- ACTUAL PROOF OF String.ne_of_lt -/

example {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction