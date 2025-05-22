import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).maximum? = some a := by
  rw [replicate_eq_cons]
  rw [maximum?_cons_of_max (le_of_max_eq w)]
  exact some_inj.mp (maximum?_singleton.symm)

/- ACTUAL PROOF OF List.maximum?_replicate_of_pos -/

example [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).maximum? = some a := by
  simp [maximum?_replicate, Nat.ne_of_gt h, w]