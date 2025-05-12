import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  unfold enumFrom
  simp only [mem_bind, mem_map, Prod.exists, mem_range, exists_prop, mem_get?_eq]
  split
  · rintro ⟨j, hj1, hj2⟩
    use j
    constructor
    · linarith
    · exact hj2
  · rintro ⟨j, hj1, hj2⟩
    use j
    constructor
    · linarith
    · exact hj2

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]