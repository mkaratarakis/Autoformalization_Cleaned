import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (f : β → α) (l : List β) : find? p (l.map f) = (l.find? (p ∘ f)).map f := by
  induction l with
  | nil =>
    simp [find?, map]
  | cons x xs ih =>
    simp [find?, map]
    by_cases h : p (f x)
    · simp [h]
    · simp [h, ih]

/- ACTUAL PROOF OF List.find?_map -/

example (f : β → α) (l : List β) : find? p (l.map f) = (l.find? (p ∘ f)).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, find?]
    by_cases h : p (f x) <;> simp [h, ih]