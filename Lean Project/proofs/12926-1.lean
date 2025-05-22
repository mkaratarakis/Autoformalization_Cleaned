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
    cases' h with h₁ h₂
    · simp only [count]
      exact Nat.zero_lt_succ _
    · simp only [count]
      apply Nat.succ_lt_succ
      exact h₂

/- ACTUAL PROOF OF List.count_pos_iff_mem -/

example {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos, beq_iff_eq, exists_eq_right]