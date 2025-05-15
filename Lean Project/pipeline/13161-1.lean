import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp only [enumFrom, mem_map, Prod.mk.inj_iff, mem_zipWithIndex, forall_mem_zipIdx]
  constructor
  · intro h
    have h' : l.get? i = some x := by
      simpa using h
    exact h'
  · intro h
    have h' : (n + i, x) ∈ enumFrom n l := by
      simpa using h
    exact h'

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]