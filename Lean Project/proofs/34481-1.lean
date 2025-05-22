import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) : (l.takeWhile p).head? = l.head?.filter p := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    by_cases h : p x
    · simp [h]
    · simp [h]

/- ACTUAL PROOF OF List.head?_takeWhile -/

example (p : α → Bool) (l : List α) : (l.takeWhile p).head? = l.head?.filter p := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head?_cons, Option.filter_some]
    split <;> simp