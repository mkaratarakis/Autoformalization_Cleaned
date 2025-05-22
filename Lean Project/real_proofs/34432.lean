import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat


example {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by
  simp [Nodup]