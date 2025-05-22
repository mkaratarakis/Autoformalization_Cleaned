import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  constructor
  · intro h
    apply And.intro
    · intro hmem
      exact absurd hmem (Pairwise.nodup_cons.1 h)
    · exact Pairwise.nodup_cons.2 h
  · rintro ⟨hmem, hnodup⟩
    apply Pairwise.nodup_cons
    · assumption
    · intros b hb
      exact hmem hb

/- ACTUAL PROOF OF List.nodup_cons -/

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]