import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  constructor
  · intro h
    rw [count] at h
    simp only [Nat.zero_lt_succ_iff] at h
    cases l <;> simp
    · contradiction
    · simp
      apply Or.inr
      exact h
    · simp
      apply Or.inl
      exact h_a
  · intro h
    induction l generalizing a
    · simp
    · cases h
    · simp [count]
      apply Nat.pos_of_ne_zero
      apply ne_of_mem_of_not_mem
      · exact h
      · intro h'
        apply h
        simp [h']

/- ACTUAL PROOF OF List.count_pos_iff_mem -/

example {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos, beq_iff_eq, exists_eq_right]