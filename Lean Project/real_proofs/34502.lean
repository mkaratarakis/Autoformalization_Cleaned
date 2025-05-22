import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


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