import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) :
    (replicate n a).dropWhile p = (replicate n a).filter (fun a => !p a) := by
  induction n with
  | zero =>
    simp [replicate]
  | succ k ih =>
    simp [replicate]
    by_cases h : p a
    · simp [h, ih]
    · simp [h]

/- ACTUAL PROOF OF List.dropWhile_replicate_eq_filter_not -/

example (p : α → Bool) :
    (replicate n a).dropWhile p = (replicate n a).filter (fun a => !p a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, dropWhile_cons]
    split <;> simp_all