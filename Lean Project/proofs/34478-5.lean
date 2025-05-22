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
    rw [dropWhile]
    split
    next =>
      have : p x = true := h x (List.Mem.head _ _)
      simp [this]
      exact ih fun a m => h a (List.Mem.tail _ m)
    next =>
      exact (List.mem_cons_self _ _).elim

/- ACTUAL PROOF OF List.dropWhile_append_of_pos -/

example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [dropWhile_cons]