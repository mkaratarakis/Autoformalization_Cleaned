import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
    constructor
    · intro h
      have h' : l[i]? = some x := by
        simpa [zipIdx, List.mem_zipIdx] using h
      exact h'
    · intro h
      have h' : (n+i, x) ∈ zipIdx n l := by
        simpa [zipIdx, List.mem_zipIdx] using h
      exact h'

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]