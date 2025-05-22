import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  induction l
  · rfl
  · simp [map, zip]
    exact tail_ih

/- ACTUAL PROOF OF List.map_prod_right_eq_zip -/

example {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  exact map_id _