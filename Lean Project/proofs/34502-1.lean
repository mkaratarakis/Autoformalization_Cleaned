import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {xs ys : List α} :
    (xs ++ ys).takeWhile p =
      if (xs.takeWhile p).length = xs.length then xs ++ ys.takeWhile p else xs.takeWhile p := by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    by_cases h : p x
    · simp [takeWhile, h]
      rw [ih]
      split
      · rw [length_cons, ih.left]
        simp
      · rw [ih.right]
    · simp [takeWhile, h]
      rw [length_nil, Nat.zero_eq]
      split
      · exfalso
        simp [length_nil, Nat.zero_eq]
      · simp

/- ACTUAL PROOF OF List.takeWhile_append -/

example {xs ys : List α} :
    (xs ++ ys).takeWhile p =
      if (xs.takeWhile p).length = xs.length then xs ++ ys.takeWhile p else xs.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, takeWhile_cons]
    split
    · simp_all only [length_cons, add_one_inj]
      split <;> rfl
    · simp_all