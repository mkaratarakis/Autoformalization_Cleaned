import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  let l' := l.dropWhile p
  have h1 : l'.head? = some (l'.head w) := by
    rw [head?_eq_iff_ne_nil]
    exact w
  exact (dropWhile_eq_nil_iff_or_and _ _).mp (by simp [h1]) w
  apply not_head_dropWhile
  exact w

/- ACTUAL PROOF OF List.head_dropWhile_not -/

example (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  simpa [head?_eq_head, w] using head?_dropWhile_not p l