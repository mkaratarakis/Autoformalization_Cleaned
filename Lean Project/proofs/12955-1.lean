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
    apply List.ball_of_countP_eq_length
    · exact h1
    · intro b h2
      exact (beq_of_eq (List.countP_eq_length.1 h1 h2)).symm
  · intro h1
    apply List.countP_eq_length.2
    · intro b h2
      exact (eq_of_beq (h1 b h2)).symm
    · exact h1

/- ACTUAL PROOF OF List.count_eq_length -/

example {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  rw [count, countP_eq_length]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]