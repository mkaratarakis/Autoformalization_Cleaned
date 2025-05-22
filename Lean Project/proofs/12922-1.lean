import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  constructor
  · intro h
    have h1 : 0 < length (filter p l) := h
    have h2 : ∃ a, a ∈ filter p l := by
      cases h1 with
      | succ n =>
        have h3 : n < length (filter p l) := Nat.lt_of_succ_lt_succ h1
        exact Exists.elim (List.nthLe_mem _ _) h3
    cases h2 with
    | intro a h3 =>
      have h4 : a ∈ l ∧ p a = true := by
        simp [List.mem_filter] at h3
        exact h3
      exact Exists.intro a h4
  · intro h
    cases h with
    | intro a h1 =>
      have h2 : a ∈ filter p l := by
        simp [List.mem_filter]
        exact h1
      have h3 : 0 < length (filter p l) := by
        cases h2 with
        | intro h4 h5 =>
          exact Nat.succ_pos'
      exact h3

/- ACTUAL PROOF OF List.countP_pos -/

example : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  simp only [countP_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]