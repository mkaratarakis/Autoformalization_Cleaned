import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil =>
    rfl
  | cons x xs ih =>
    simp
    rw [ih]

/- ACTUAL PROOF OF List.dropWhile_append_of_pos -/

example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [dropWhile_cons]