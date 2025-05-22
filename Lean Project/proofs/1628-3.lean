import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) (l : List α) (f : α → β) :
    zipIdx (List.range n) (l.map f) = (zipIdx (List.range n) l).map (Prod.map id f) := by
  induction l with
  | nil =>
    simp
  | cons hd tl IH =>
    simp [zipIdx, map]
    rw [IH]
    simp [Prod.map, Function.comp]
    rfl

/- ACTUAL PROOF OF List.enumFrom_map -/

example (n : Nat) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction l with
  | nil => rfl
  | cons hd tl IH =>
    rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    rfl