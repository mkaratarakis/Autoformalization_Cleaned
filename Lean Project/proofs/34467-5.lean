import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  by_cases h : p a = true
  · simp [h]
    rfl
  · simp [h]
    rw [takeWhile_eq_nil_of_not]
    exact h

/- ACTUAL PROOF OF List.takeWhile_replicate -/

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_replicate_eq_filter, filter_replicate]