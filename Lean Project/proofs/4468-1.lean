import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  constructor
  · intro h
    exact eq_nil_of_length_eq_zero (eq_nil_of_minimum?_eq_none h)
  · intro h
    rw [h]
    exact minimum?_nil

/- ACTUAL PROOF OF List.minimum?_eq_none_iff -/

example {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]