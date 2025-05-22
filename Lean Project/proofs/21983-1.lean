import Init.Data.Char.Lemmas
import Init.Data.String.Lemmas

open String


example {a b : String} (h : a < b) : a ≠ b := by
  intro h_eq
  apply h_eq at h
  exact lt_irrefl a h

/- ACTUAL PROOF OF String.ne_of_lt -/

example {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction