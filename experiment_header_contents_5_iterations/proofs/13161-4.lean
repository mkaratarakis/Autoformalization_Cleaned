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
      rw [enumFrom.eq_def, mem_map, mem_zipWithIndex] at h
      obtain ⟨j, hj1, hj2⟩ := h
      rw [Nat.add_sub_cancel_left] at hj2
      cases' hj2 with k hk
      · exfalso
        exact Nat.not_lt_zero i hj1
      · exact hk
    · intro h
      rw [enumFrom.eq_def, mem_map, mem_zipWithIndex]
      use i
      constructor
      · exact Nat.lt_add_right _ _ _
      · rw [h]

/- ACTUAL PROOF OF List.mk_add_mem_enumFrom_iff_get? -/

example {n i : ℕ} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l.get? i = x := by
  simp [mem_iff_get?]