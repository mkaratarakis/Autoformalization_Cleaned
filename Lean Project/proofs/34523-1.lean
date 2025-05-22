import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).takeWhile p = (l.takeWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil =>
    rfl
  | cons x xs ih =>
    match f x with
    | none =>
      apply takeWhile_cons
      apply Option.all_none
      rw [ih]
    | some b =>
      by_cases h : p b = true
      · apply takeWhile_cons
        rw [ih]
        simp [h]
      · apply takeWhile_nil
        rw [ih]
        simp [h]

/- ACTUAL PROOF OF List.takeWhile_filterMap -/

example (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).takeWhile p = (l.takeWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;> rename_i h
    · simp only [takeWhile_cons, h]
      split <;> simp_all
    · simp [takeWhile_cons, h, ih]
      split <;> simp_all [filterMap_cons]