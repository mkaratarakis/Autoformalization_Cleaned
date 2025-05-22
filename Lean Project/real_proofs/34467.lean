import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_replicate_eq_filter, filter_replicate]