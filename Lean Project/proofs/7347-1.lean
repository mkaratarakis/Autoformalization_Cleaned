import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (n) (l : List α) : length (take n l) ≤ n := by
  rw [length_take]
  exact min_le_left n (length l)

/- ACTUAL PROOF OF List.length_take_le -/

example (n) (l : List α) : length (take n l) ≤ n := by
  simp [Nat.min_le_left]