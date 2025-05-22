import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  induction l
  · rfl
  · simp [map, zip]
    exact a_1

/- ACTUAL PROOF OF List.map_prod_left_eq_zip -/

example {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  exact map_id _