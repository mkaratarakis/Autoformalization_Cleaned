import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) (x : α) (xs : List α) :
    zipIdx n (x :: xs) = (n, x) :: (zipIdx n xs).map (Prod.map (· + 1) id) := by
  rw [zipIdx]
  rw [add_comm n 1]
  rw [← zipIdx]
  rw [← map_zipIdx_index]

/- ACTUAL PROOF OF List.enumFrom_cons' -/

example (n : Nat) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map (· + 1) id) := by
  rw [enumFrom_cons, Nat.add_comm, ← map_fst_add_enumFrom_eq_enumFrom]