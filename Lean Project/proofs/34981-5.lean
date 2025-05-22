import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← append_assoc l₁ l₂ l₃]
  apply Sublist.append_right
  apply Sublist.refl

/- ACTUAL PROOF OF List.infix_append' -/

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append