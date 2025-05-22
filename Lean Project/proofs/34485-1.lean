import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).dropWhile p = (l.dropWhile (p ∘ f)).map f := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp [dropWhile, map]
    cases h : p (f x)
    · simp [h, ih]
    · simp [h]

/- ACTUAL PROOF OF List.dropWhile_map -/

example (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).dropWhile p = (l.dropWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [map_cons, dropWhile_cons]
    split <;> simp_all