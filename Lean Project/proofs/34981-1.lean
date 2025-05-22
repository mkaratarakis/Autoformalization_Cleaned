import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [append_assoc]
  apply Sublist.append_right
  apply contiguous_substring_of_append
example {α : Type u} : ∀{l₁ l₂ l₃ : List α}, l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃

theorem contiguous_substring_of_append {α : Type u} : ∀{l₁ l₂ : List α}, l₂ <:+: l₁ ++ l₂

/- ACTUAL PROOF OF List.infix_append' -/

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append