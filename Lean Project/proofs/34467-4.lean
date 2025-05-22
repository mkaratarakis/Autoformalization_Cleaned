import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  by_cases h : p a = true
  · simp [h]
    exact takeWhile_eq_self.mpr h
  · simp [h]
    exact takeWhile_eq_nil.mpr (not_not.mpr h)

/- ACTUAL PROOF OF List.takeWhile_replicate -/

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_replicate_eq_filter, filter_replicate]