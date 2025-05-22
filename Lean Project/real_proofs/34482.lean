import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [takeWhile_cons]