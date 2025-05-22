import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {p : α → Bool} {a : α} {l : List α} (h : ¬ p a) :
    (a :: l).takeWhile p = [] := by
  rw [takeWhile]
  split
  · intro contra
    apply h
    assumption
  · rfl

/- ACTUAL PROOF OF List.takeWhile_cons_of_neg -/

example {p : α → Bool} {a : α} {l : List α} (h : ¬ p a) :
    (a :: l).takeWhile p = [] := by
  simp [takeWhile_cons, h]