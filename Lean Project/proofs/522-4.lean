import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = length l - 1 := by
  have h : ∃ (l1 l2 : List α), l = l1 ++ a :: l2 ∧ (l.eraseP p = l1 ++ l2) ∧ (∀ x, x ∈ l1 → ¬p x) := by
    {
      apply exists_of_mem_eraseP
      exact al
    }
  obtain ⟨l1, l2, h1, h2, h3⟩ := h
  dsimp [eraseP]
  rw [← h1, length, ← h1, length, length_append, length_append, length_cons]
  calc
    length l = length (l1 ++ a :: l2) := by rw [h1]
    _ = length l1 + length (a :: l2) := by rw [length_append]
    _ = length l1 + (length l2 + 1) := by rw [length_cons]
    _ = (length l1 + length l2) + 1 := by rw [add_assoc]
  rw [← h2, length]
  calc
    length (eraseP p l) = length (l1 ++ l2) := by rw [h2]
    _ = length l1 + length l2 := by rw [length_append]
  linarith

/- ACTUAL PROOF OF List.length_eraseP_of_mem -/

example (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = length l - 1 := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [length_append, e₁]; rfl