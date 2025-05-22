import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if (xs.dropWhile p).isEmpty then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil =>
    simp
  | cons h t ih =>
    by_cases hp : p h
    · simp [hp]
      rw [ih]
      split
      · rintro rfl
        simp
      · intro h1
        simp
    · simp [hp]
      rw [dropWhile_cons_false hp]

/- ACTUAL PROOF OF List.dropWhile_append -/

example {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if (xs.dropWhile p).isEmpty then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil => simp
  | cons h t ih =>
    simp only [cons_append, dropWhile_cons]
    split <;> simp_all