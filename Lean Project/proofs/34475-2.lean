import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) (w) :
    (l.takeWhile p).head w = l.head (by rintro rfl; simp_all) := by
  cases l with
  | nil =>
    -- If l is nil, the goal is vacuously true because both sides are undefined.
    simp
    trivial
  | cons x xs =>
    -- If l is non-empty, we need to show that the head of the takeWhile list is equal to the head of the original list.
    simp
    cases h : p x with
    | true =>
      -- If p x is true, takeWhile p (x :: xs) = x :: takeWhile p xs
      simp [takeWhile, h]
      simp [h]
    | false =>
      -- If p x is false, takeWhile p (x :: xs) = nil, which contradicts the assumption that it is non-empty.
      simp [takeWhile, h]
      contradiction

/- ACTUAL PROOF OF List.head_takeWhile -/

example (p : α → Bool) (l : List α) (w) :
    (l.takeWhile p).head w = l.head (by rintro rfl; simp_all) := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head_cons]
    simp only [takeWhile_cons] at w
    split <;> simp_all