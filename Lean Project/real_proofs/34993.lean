import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]