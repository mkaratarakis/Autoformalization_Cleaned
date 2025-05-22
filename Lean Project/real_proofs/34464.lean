import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (l : List α) : l.dropLast = l.take (l.length - 1) := by
  cases l with
  | nil => simp [dropLast]
  | cons x l =>
    induction l generalizing x <;> simp_all [dropLast]