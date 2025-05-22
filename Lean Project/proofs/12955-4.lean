import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  constructor
  · intro h1
    intro b hb
    have h2 : count a l = length l := h1
    rw [count] at h2
    induction l generalizing b
    · contradiction
    · case cons x xs ih =>
      simp at h2
      cases hb <;> simp at hb
      · exact hb
      · apply ih
        exact hb
  · intro h1
    induction l
    · rfl
    · case cons x xs ih =>
      simp
      by_cases h : x = a
      · rw [h]
        exact ih (forall_mem_of_forall_mem_cons h1)
      · simp [h]
        rw [count_cons_ne _ _ _ h]
        exact ih (forall_mem_of_forall_mem_cons h1)

/- ACTUAL PROOF OF List.count_eq_length -/

example {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  rw [count, countP_eq_length]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]