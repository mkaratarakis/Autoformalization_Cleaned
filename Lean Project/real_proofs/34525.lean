import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).dropWhile p = (l.dropWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;> rename_i h
    · simp only [dropWhile_cons, h]
      split <;> simp_all
    · simp [dropWhile_cons, h, ih]
      split <;> simp_all [filterMap_cons]