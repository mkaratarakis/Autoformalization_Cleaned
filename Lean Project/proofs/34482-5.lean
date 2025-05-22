import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil =>
    simp
  | cons x xs ih =>
    have h' : ∀ a ∈ xs, p a := by
      intro a ha
      apply h
      exact List.mem_cons_of_mem _ ha
    simp [takeWhile, ih h']
    split
    · exact (h x (List.mem_cons_self x xs)).symm
    · rfl

/- ACTUAL PROOF OF List.takeWhile_append_of_pos -/

example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [takeWhile_cons]