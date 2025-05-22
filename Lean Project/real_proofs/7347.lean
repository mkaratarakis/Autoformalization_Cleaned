import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (n) (l : List α) : length (take n l) ≤ n := by
  simp [Nat.min_le_left]