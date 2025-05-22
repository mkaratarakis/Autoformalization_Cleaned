import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example {xs : List α} [Min α] : xs.min? = none ↔ xs = [] := by
  constructor
  · intro h
    cases xs
    · exact rfl
    · cases h
  · intro h
    rw [h]
    exact min?_nil

/- ACTUAL PROOF OF List.minimum?_eq_none_iff -/

example {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]