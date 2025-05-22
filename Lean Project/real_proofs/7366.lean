import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (h : n ≤ length l) : length (take n l) = n := by
  simp [Nat.min_eq_left h]