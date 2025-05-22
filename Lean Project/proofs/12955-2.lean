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
    apply mem_of_count_eq_length h1 hb
  · intro h1
    apply count_eq_length_of_mem h1

/- ACTUAL PROOF OF List.count_eq_length -/

example {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  rw [count, countP_eq_length]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]