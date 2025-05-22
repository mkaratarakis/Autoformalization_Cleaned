import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (f : β → γ) (l : List β) : findSome? p (l.map f) = l.findSome? (p ∘ f) := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp
    by_cases h : (p (f x)) = none
    · simp [h]
      exact ih
    · have : ∃ a, (p (f x)) = some a
      exact Option.ne_none_iff_exists.mp h
      rcases this with ⟨b, hb⟩
      simp [hb]

/- ACTUAL PROOF OF List.findSome?_map -/

example (f : β → γ) (l : List β) : findSome? p (l.map f) = l.findSome? (p ∘ f) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, findSome?]
    split <;> simp_all