import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  constructor
  · intro h
    rw [countP_eq_length_filter] at h
    have h1 : 0 < length (filter p l) := h
    cases h1 with
    | succ n =>
      let a := nthLe (filter p l) n (Nat.lt_of_succ_lt_succ h1)
      have ha : a ∈ filter p l := nthLe_mem _ _ _
      simp [mem_filter] at ha
      exact ⟨a, ha.left, ha.right⟩
  · rintro ⟨a, ha, rfl⟩
    rw [countP_eq_length_filter]
    exact length_pos_of_mem_filter ⟨ha, rfl⟩

/- ACTUAL PROOF OF List.countP_pos -/

example : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  simp only [countP_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]