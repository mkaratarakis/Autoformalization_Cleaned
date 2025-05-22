import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) : l.dropLast = l.take (l.length - 1) := by
  induction l with
  | nil =>
    simp [dropLast, take, length]
  | cons x l ih =>
    simp [dropLast, take, length]
    rw [ih]

/- ACTUAL PROOF OF List.dropLast_eq_take -/

example (l : List α) : l.dropLast = l.take (l.length - 1) := by
  cases l with
  | nil => simp [dropLast]
  | cons x l =>
    induction l generalizing x <;> simp_all [dropLast]