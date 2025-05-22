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
    simp at h
    cases' l with b l <;> simp at h
    · exact absurd h (by decide)
    · simp [count]
      exact Nat.succ_pos _
    · cases h
      · simp [count]
        exact Nat.succ_pos _
      · simp [count]
        exact Nat.succ_pos _
  · intro h
    induction l generalizing a
    · simp
    · cases h
      · simp [count]
        exact Nat.succ_pos _
      · exact l_ih h

/- ACTUAL PROOF OF List.count_pos_iff_mem -/

example {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos, beq_iff_eq, exists_eq_right]