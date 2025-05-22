import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← append_assoc l₁ l₂ l₃]
  rw [nil_append]
  rw [append_nil]
  rw [append_assoc]
  exact Sublist.subset_append_right (Sublist.subset_append_left (Sublist.refl l₂))

/- ACTUAL PROOF OF List.infix_append' -/

example (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append