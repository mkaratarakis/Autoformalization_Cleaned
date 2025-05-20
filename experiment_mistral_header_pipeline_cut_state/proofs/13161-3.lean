import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = some x := by
  constructor
  · intro h
    simp at h
    exact h
  · rintro ⟨_, rfl⟩
    simp
    exact mem_enumFrom.2 ⟨i, rfl, rfl⟩

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]