import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {n : Nat} {a : α} {l : List α} : replicate n a ⊆ l ↔ n = 0 ∨ a ∈ l := by
  induction n with
  | zero => simp
  | succ n ih => simp (config := {contextual := true}) [replicate_succ, ih, cons_subset]