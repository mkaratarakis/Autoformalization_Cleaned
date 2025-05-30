import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat


example {n : Nat} {a : α} (h : ¬p a) :
    (replicate n a).eraseP p = replicate n a := by
  rw [eraseP_of_forall_not (by simp_all)]