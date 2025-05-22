import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example {xs : List α} [Max α] : xs.max? = none ↔ xs = [] := by
  constructor
  · intro h
    cases xs
    · exact rfl
    · exact absurd h (mt List.max?_eq_none.mpr rfl)
  · intro h
    rw [h]
    exact List.max?_nil

/- ACTUAL PROOF OF List.maximum?_eq_none_iff -/

example {xs : List α} [Max α] : xs.maximum? = none ↔ xs = [] := by
  cases xs <;> simp [maximum?]