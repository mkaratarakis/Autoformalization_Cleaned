import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat


example {n : Nat} {a : α} (h : p a) :
    (replicate n a).eraseP p = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ, h]