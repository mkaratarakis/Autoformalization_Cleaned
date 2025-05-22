import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} : (l.takeWhile p).all p = true := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    by_cases hp : p h
    · simp [hp, ih]
    · simp [hp]

/- ACTUAL PROOF OF List.all_takeWhile -/

example {l : List α} : (l.takeWhile p).all p = true := by
  induction l with
  | nil => rfl
  | cons h t ih => by_cases p h <;> simp_all