import Init.Data.List.Count
import Init.Data.List.MinMax
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.Basic

open List
open Nat


example (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]