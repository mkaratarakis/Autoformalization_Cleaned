import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix]; simp only [reverse_reverse]