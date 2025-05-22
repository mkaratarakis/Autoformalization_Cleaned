import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} {k : Nat} : l.take k = [] ↔ k = 0 ∨ l = [] := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]