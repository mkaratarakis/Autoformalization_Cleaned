import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enumFrom_map_fst, range_eq_range']