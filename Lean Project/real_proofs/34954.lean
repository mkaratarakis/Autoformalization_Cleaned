import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  simp [isSuffixOf, all_eq]