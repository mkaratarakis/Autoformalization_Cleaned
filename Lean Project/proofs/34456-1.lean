import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  let l' := l.dropWhile p
  have h1 : l'.head? = some (l'.head w) := by
    apply head?_eq_some_of_ne_nil
    assumption
  have h2 : ∀ {l : List α} {p : α → Bool}, l.dropWhile p ≠ [] → ¬p (head (l.dropWhile p) h1) := by
    intro l p h
    apply not_head_dropWhile
    assumption
  rw [← h1] at h2
  exact h2

/- ACTUAL PROOF OF List.head_dropWhile_not -/

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  simpa [head?_eq_head, w] using head?_dropWhile_not p l