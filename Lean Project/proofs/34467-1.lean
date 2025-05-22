import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_eq_filter]
  split
  · intro h
    rw [filter_replicate h]
  · intro h
    rw [filter_replicate h]
    rfl

/- ACTUAL PROOF OF List.takeWhile_replicate -/

example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_replicate_eq_filter, filter_replicate]