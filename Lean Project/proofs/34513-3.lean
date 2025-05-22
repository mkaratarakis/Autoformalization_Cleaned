import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} :
    (l.dropWhile p).any (fun x => !p x) = !l.all p := by
  induction l with
  | nil =>
    simp [List.dropWhile, List.any, List.all]
  | cons h t ih =>
    by_cases hp : p h
    · simp [hp, List.dropWhile, List.any, List.all]
      exact ih
    · have hnp : ¬ p h := by simpa using hp
      simp [hnp, List.dropWhile, List.any, List.all]

/- ACTUAL PROOF OF List.any_dropWhile -/

example {l : List α} :
    (l.dropWhile p).any (fun x => !p x) = !l.all p := by
  induction l with
  | nil => rfl
  | cons h t ih => by_cases p h <;> simp_all