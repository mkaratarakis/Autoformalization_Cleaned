import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat


example {l : List α} :
    l.reverse.Pairwise R ↔ l.Pairwise (fun a b => R b a) := by
  induction l <;> simp [*, pairwise_append, and_comm]