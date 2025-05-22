import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat


example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]