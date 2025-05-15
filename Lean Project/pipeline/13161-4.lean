import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ l.zipIdx ↔ l[i]? = some x := by
  constructor
  · intro h
    rw [mem_zipIdx] at h
    exact h
  · intro h
    rw [mem_zipIdx]
    exact h

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]