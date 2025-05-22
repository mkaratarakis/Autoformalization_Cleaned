import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) :
    (replicate n a).dropWhile p = if p a then [] else replicate n a := by
  rw [dropWhile_eq_filter_not]
  rw [filter_replicate]
  split <;> simp

/- ACTUAL PROOF OF List.dropWhile_replicate -/

example (p : α → Bool) :
    (replicate n a).dropWhile p = if p a then [] else replicate n a := by
  simp only [dropWhile_replicate_eq_filter_not, filter_replicate]
  split <;> simp_all