import Init.Data.Char.Lemmas
import Init.Data.String.Lemmas

open String


example {a b : String} (h : a < b) : a ≠ b := by
  intro h_eq
  rw [h_eq] at h
  exact not_lt_of_le (le_refl b) h

/- ACTUAL PROOF OF String.ne_of_lt -/

example {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction