import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat


example (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = length l - 1 := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [length_append, e₁]; rfl