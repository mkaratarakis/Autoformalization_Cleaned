import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) :
    match (l.dropWhile p).head? with | some x => p x = false | none => True := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    by_cases h : p x = true
    · simp [dropWhile, h]
      exact ih
    · simp [dropWhile, h]
      rw [head?_cons]
      simp [h]

/- ACTUAL PROOF OF List.head?_dropWhile_not -/

example (p : α → Bool) (l : List α) :
    match (l.dropWhile p).head? with | some x => p x = false | none => True := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [dropWhile_cons]
    split <;> rename_i h <;> split at h <;> simp_all