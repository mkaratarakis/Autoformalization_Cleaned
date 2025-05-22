import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat


example {l : List α} (H : ∀ x y, R x y) : Pairwise R l := by
  induction l <;> simp [*]