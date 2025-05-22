import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (m n : Nat) : take m (range n) = range (min m n) := by
  funext m n
  apply List.ext
  · simp [List.length_take, List.length_range, min_def]
  · intros i h
    simp [List.nthLe_take, List.nthLe_range]
    rw [min_def] at h
    cases h with
    | inl h₁ =>
      simp [h₁]
    | inr h₂ =>
      simp [h₂]

/- ACTUAL PROOF OF List.take_range -/

example (m n : Nat) : take m (range n) = range (min m n) := by
  apply List.ext_getElem
  · simp
  · simp (config := { contextual := true }) [← getElem_take, Nat.lt_min]