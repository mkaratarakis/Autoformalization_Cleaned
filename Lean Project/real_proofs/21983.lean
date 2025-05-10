import Init.Data.Char.Lemmas
import Init.Data.String.Lemmas

open String



example {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction