import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  let l' := l.dropWhile p
  have h1 : l'.head? = some (l'.head w) := by
    simp [head?, head]
    exact w
  rw [← h1]
  apply dropWhile_head_not_mem
  exact w

/- ACTUAL PROOF OF List.head_dropWhile_not -/

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  simpa [head?_eq_head, w] using head?_dropWhile_not p l