import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (f : α → β) (n : Nat) (l : List α) :
    map (Prod.map id f) (enumFrom n l) = enumFrom n (map f l) := by
  induction l with
  | nil =>
    simp [enumFrom, map]
  | cons head tail ih =>
    simp [enumFrom, map, Prod.map]
    rw [ih]

/- ACTUAL PROOF OF List.map_enumFrom -/

example (f : α → β) (n : Nat) (l : List α) :
    map (Prod.map id f) (enumFrom n l) = enumFrom n (map f l) := by
  induction l generalizing n <;> simp_all