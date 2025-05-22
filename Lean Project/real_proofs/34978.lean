import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  simp [isSuffixOf]