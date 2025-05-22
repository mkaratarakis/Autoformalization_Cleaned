import Init.Data.List.Count
import Init.Data.List.MinMax
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.Basic

open List
open Nat

example (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  rw [leftpad]
  split
  · simp [length, replicate, max_eq_left (le_max_right _ _)]
  · simp [length, replicate, max_eq_right (le_max_left _ _)]

/- ACTUAL PROOF OF List.leftpad_length -/

example (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]