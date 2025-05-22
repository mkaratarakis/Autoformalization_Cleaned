import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) (x : α) (xs : List α) :
    zipIdx (x :: xs) n = (n, x) :: (zipIdx xs (n + 1)) := by
  rw [zipIdx]
  rw [zipIdx]
  simp

/- ACTUAL PROOF OF List.enumFrom_cons' -/

example (n : Nat) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map (· + 1) id) := by
  rw [enumFrom_cons, Nat.add_comm, ← map_fst_add_enumFrom_eq_enumFrom]