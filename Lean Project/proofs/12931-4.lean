import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (l : List α) (a : α) : l.filter (· == a) = replicate (count a l) a := by
  induction l with
  | nil =>
    simp [filter, replicate]
  | cons h t ih =>
    simp [filter, replicate]
    split
    · next x hx =>
      simp [count] at hx
      rw [ih]
      simp [count]
    · next hne =>
      simp [count] at hne
      rw [ih]

/- ACTUAL PROOF OF List.filter_beq -/

example (l : List α) (a : α) : l.filter (· == a) = replicate (count a l) a := by
  simp only [count, countP_eq_length_filter, eq_replicate, mem_filter, beq_iff_eq]
  exact ⟨trivial, fun _ h => h.2⟩