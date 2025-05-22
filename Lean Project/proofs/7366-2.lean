import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (h : n ≤ length l) : length (take n l) = n := by
  rw [length_take]
  exact min_eq_left h

/- ACTUAL PROOF OF List.length_take_of_le -/

example (h : n ≤ length l) : length (take n l) = n := by
  simp [Nat.min_eq_left h]